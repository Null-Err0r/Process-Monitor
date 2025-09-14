package main

import (
	"fmt"
	"io"
	"net"
	"net/http"
	"os"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/gdamore/tcell/v2"
	"github.com/pkg/browser"
	"github.com/rivo/tview"
	pscpu "github.com/shirou/gopsutil/v3/cpu"
	pshost "github.com/shirou/gopsutil/v3/host"
	psmem "github.com/shirou/gopsutil/v3/mem"
	psnet "github.com/shirou/gopsutil/v3/net"
	psproc "github.com/shirou/gopsutil/v3/process"
)

type AppTheme struct {
	BackgroundColor    tcell.Color
	PrimaryTextColor   tcell.Color
	BorderColor        tcell.Color
	TitleColor         tcell.Color
	FocusColor         tcell.Color
	SubtleTextColor    tcell.Color
	SafeColor          tcell.Color
	NetworkColor       tcell.Color
	WarningColor       tcell.Color
	DangerColor        tcell.Color
	CriticalColor      tcell.Color
	DeletedColor       tcell.Color
	ButtonBgColor      tcell.Color
	ButtonTextColor    tcell.Color
}

var theme = AppTheme{
	BackgroundColor:    tcell.NewHexColor(0x2E3440),
	PrimaryTextColor:   tcell.NewHexColor(0xECEFF4),
	BorderColor:        tcell.NewHexColor(0x4C566A),
	TitleColor:         tcell.NewHexColor(0x88C0D0),
	FocusColor:         tcell.NewHexColor(0x81A1C1),
	SubtleTextColor:    tcell.NewHexColor(0x4C566A),
	SafeColor:          tcell.NewHexColor(0xA3BE8C),
	NetworkColor:       tcell.NewHexColor(0x8FBCBB),
	WarningColor:       tcell.NewHexColor(0xEBCB8B),
	DangerColor:        tcell.NewHexColor(0xBF616A),
	CriticalColor:      tcell.NewHexColor(0xB48EAD),
	DeletedColor:       tcell.NewHexColor(0xD08770),
	ButtonBgColor:      tcell.NewHexColor(0x434C5E),
	ButtonTextColor:    tcell.NewHexColor(0xECEFF4),
}

type AppState struct {
	sync.RWMutex
	AllProcs    map[int32]*ProcessInfo
	RootPIDs    []int32
	RulesEngine *RulesEngine
	SortBy      string
	SortAsc     bool
	lockedPID   int32
	SearchQuery string
	SearchMode  string
	PublicIP    string
}

type ProcessInfo struct {
	Process    *psproc.Process
	Name       string
	Username   string
	Exe        string
	Cmdline    string
	Status     string
	CPU        float64
	Mem        float32
	Ppid       int32
	IsDeleted  bool
	Children   []*ProcessInfo
	NetCons    []psnet.ConnectionStat
	CreateTime int64
	Threads    int32
	OpenFiles  []string
	ParentInfo *ProcessInfo
	ChildCount int
	Level      int
}

type MainView struct {
	Grid               *tview.Grid
	DetailBox          *tview.TextView
	Search             *tview.InputField
	ClearSearchButton  *tview.Button
	SearchModeSelector *tview.DropDown
	ProcessTree        *tview.TreeView
	SystemInfo         *tview.TextView
	ThreatPanel        *tview.TextView
	ThreatList         *tview.TextView
	FreezeButton       *tview.Button
	Pages              *tview.Pages
	HelpButton         *tview.Button
	AboutButton        *tview.Button
}

type RuleCondition struct {
	Field    string
	Operator string
	Value    any
}

type Rule struct {
	Name        string
	Description string
	Severity    string
	Conditions  []RuleCondition
}

type RulesEngine struct {
	rules []Rule
}

var (
	dnsCache = make(map[string]string)
	dnsMutex = &sync.Mutex{}
	app      *tview.Application
)

func openURL(url string) {
	_ = browser.OpenURL(url)
}

func NewState() *AppState {
	return &AppState{
		AllProcs:    make(map[int32]*ProcessInfo),
		RootPIDs:    []int32{},
		SortBy:      "cpu",
		SortAsc:     false,
		SearchQuery: "",
		SearchMode:  "all",
		PublicIP:    "Fetching...",
	}
}

func updatePublicIP(s *AppState) {
	client := http.Client{Timeout: 5 * time.Second}
	resp, err := client.Get("https://api.ipify.org")
	if err != nil {
		s.Lock()
		s.PublicIP = "N/A"
		s.Unlock()
		return
	}
	defer resp.Body.Close()
	ip, err := io.ReadAll(resp.Body)
	if err != nil {
		s.Lock()
		s.PublicIP = "N/A"
		s.Unlock()
		return
	}
	s.Lock()
	s.PublicIP = strings.TrimSpace(string(ip))
	s.Unlock()
}

func UpdateProcessSnapshot(s *AppState) {
	procs, err := psproc.Processes()
	if err != nil {
		return
	}
	newProcs := make(map[int32]*ProcessInfo, len(procs))
	for _, p := range procs {
		name, _ := p.Name()
		user, _ := p.Username()
		ppid, _ := p.Ppid()
		exe, _ := p.Exe()
		cmd, _ := p.Cmdline()
		status, _ := p.Status()
		createTime, _ := p.CreateTime()
		threads, _ := p.NumThreads()
		cpu, _ := p.CPUPercent()
		mem, _ := p.MemoryPercent()

		pInfo := &ProcessInfo{
			Process:    p,
			Name:       name,
			Username:   user,
			Exe:        exe,
			Cmdline:    cmd,
			Status:     strings.Join(status, ", "),
			CPU:        cpu,
			Mem:        mem,
			Ppid:       ppid,
			CreateTime: createTime,
			Threads:    threads,
			IsDeleted:  strings.HasSuffix(exe, " (deleted)"),
			Children:   make([]*ProcessInfo, 0),
		}
		newProcs[p.Pid] = pInfo
	}
	var rootPIDs []int32
	for _, pInfo := range newProcs {
		parent, parentExists := newProcs[pInfo.Ppid]
		if pInfo.Ppid == 0 || !parentExists {
			rootPIDs = append(rootPIDs, pInfo.Process.Pid)
			pInfo.Level = 0
		} else {
			parent.Children = append(parent.Children, pInfo)
			pInfo.ParentInfo = parent
			pInfo.Level = parent.Level + 1
		}
	}
	var countChildren func(*ProcessInfo)
	countChildren = func(p *ProcessInfo) {
		count := len(p.Children)
		for _, child := range p.Children {
			countChildren(child)
			count += child.ChildCount
		}
		p.ChildCount = count
	}
	for _, pid := range rootPIDs {
		if proc, ok := newProcs[pid]; ok {
			countChildren(proc)
		}
	}
	s.Lock()
	s.AllProcs = newProcs
	s.RootPIDs = rootPIDs
	s.Unlock()
}

func GetSystemSummary() (cpu, mem float64, uptime, host string, processCount int) {
	cpuPercents, _ := pscpu.Percent(0, false)
	if len(cpuPercents) > 0 {
		cpu = cpuPercents[0]
	}
	memInfo, _ := psmem.VirtualMemory()
	if memInfo != nil {
		mem = memInfo.UsedPercent
	}
	hostInfo, _ := pshost.Info()
	if hostInfo != nil {
		uptime = (time.Duration(hostInfo.Uptime) * time.Second).String()
		host = hostInfo.Hostname
	}
	procs, _ := psproc.Processes()
	processCount = len(procs)
	return
}

func NewRulesEngine() *RulesEngine {
	embeddedRules := []Rule{
		{Name: "Suspicious Path", Description: "Process running from /tmp or /dev/shm", Severity: "High",
			Conditions: []RuleCondition{{Field: "exe", Operator: "starts_with", Value: "/tmp/"}}},
		{Name: "Deleted Binary", Description: "Process executable was deleted from disk", Severity: "Critical",
			Conditions: []RuleCondition{{Field: "is_deleted", Operator: "equals", Value: true}}},
		{Name: "Root Process", Description: "Process running with root privileges", Severity: "Medium",
			Conditions: []RuleCondition{{Field: "username", Operator: "equals", Value: "root"}}},
	}
	return &RulesEngine{rules: embeddedRules}
}

func (e *RulesEngine) Evaluate(pInfo *ProcessInfo, parentInfo *ProcessInfo) *Rule {
	for _, rule := range e.rules {
		if e.match(rule, pInfo, parentInfo) {
			r := rule
			return &r
		}
	}
	return nil
}

func (e *RulesEngine) match(rule Rule, pInfo *ProcessInfo, parentInfo *ProcessInfo) bool {
	for _, cond := range rule.Conditions {
		if !checkCondition(getFieldValue(cond.Field, pInfo, parentInfo), cond.Operator, cond.Value) {
			return false
		}
	}
	return true
}

func getFieldValue(field string, pInfo *ProcessInfo, parentInfo *ProcessInfo) any {
	switch field {
	case "exe":
		return pInfo.Exe
	case "username":
		return pInfo.Username
	case "is_deleted":
		return pInfo.IsDeleted
	}
	return nil
}

func checkCondition(fieldValue any, operator string, ruleValue any) bool {
	switch operator {
	case "equals":
		return fieldValue == ruleValue
	case "starts_with":
		if s, ok := fieldValue.(string); ok {
			return strings.HasPrefix(s, ruleValue.(string))
		}
	}
	return false
}

func matchesAdvancedFilter(pInfo *ProcessInfo, query string, mode string) bool {
	if query == "" {
		return true
	}
	q := strings.ToLower(query)
	switch mode {
	case "name":
		return strings.Contains(strings.ToLower(pInfo.Name), q)
	case "pid":
		return strings.Contains(strconv.Itoa(int(pInfo.Process.Pid)), q)
	default:
		return strings.Contains(strings.ToLower(pInfo.Name), q) || strings.Contains(strconv.Itoa(int(pInfo.Process.Pid)), q) ||
			strings.Contains(strings.ToLower(pInfo.Username), q) || strings.Contains(strings.ToLower(pInfo.Exe), q)
	}
}

func createModal(content tview.Primitive, width, height int) tview.Primitive {
	return tview.NewGrid().
		SetColumns(0, width, 0).
		SetRows(0, height, 0).
		AddItem(content, 1, 1, 1, 1, 0, 0, true)
}

func NewMainView(application *tview.Application, s *AppState) *MainView {
	tview.Styles.PrimitiveBackgroundColor = theme.BackgroundColor
	tview.Styles.PrimaryTextColor = theme.PrimaryTextColor
	tview.Styles.BorderColor = theme.BorderColor
	tview.Styles.TitleColor = theme.TitleColor

	mv := &MainView{}
	app = application
	var searchTimer *time.Timer

	mv.Pages = tview.NewPages()
	mv.ProcessTree = tview.NewTreeView().SetRoot(tview.NewTreeNode("🖥️ System Processes").SetColor(theme.TitleColor)).SetCurrentNode(nil).SetTopLevel(1)
	mv.DetailBox = tview.NewTextView().SetDynamicColors(true).SetWrap(true).SetScrollable(true)
	mv.Search = tview.NewInputField().SetLabel("🔍 Search: ").SetLabelColor(theme.WarningColor).SetFieldBackgroundColor(tcell.NewHexColor(0x3B4252)).SetFieldTextColor(theme.PrimaryTextColor)
	mv.ClearSearchButton = tview.NewButton("X").SetStyle(tcell.StyleDefault.Background(theme.ButtonBgColor).Foreground(theme.DeletedColor))
	mv.SearchModeSelector = tview.NewDropDown().SetLabel("Filter: ").SetLabelColor(theme.SafeColor).SetOptions([]string{"All", "Name", "PID"}, nil).SetFieldBackgroundColor(tcell.NewHexColor(0x3B4252))
	mv.SystemInfo = tview.NewTextView().SetDynamicColors(true)
	mv.ThreatPanel = tview.NewTextView().SetDynamicColors(true)
	mv.ThreatList = tview.NewTextView().SetDynamicColors(true).SetTextAlign(tview.AlignCenter)
	mv.FreezeButton = tview.NewButton("Freeze 🥶").SetStyle(tcell.StyleDefault.Background(theme.ButtonBgColor).Foreground(theme.FocusColor))
	mv.HelpButton = tview.NewButton("Help").SetStyle(tcell.StyleDefault.Background(theme.ButtonBgColor).Foreground(theme.FocusColor))
	mv.AboutButton = tview.NewButton("About").SetStyle(tcell.StyleDefault.Background(theme.ButtonBgColor).Foreground(theme.TitleColor))

	mv.ProcessTree.SetBorder(true).SetTitle(" 🌳 Process Tree ")
	mv.DetailBox.SetBorder(true).SetTitle(" 🔬 Process Analysis ")
	mv.SystemInfo.SetBorder(true).SetTitle(" 📊 System Info ")
	mv.ThreatPanel.SetBorder(true).SetTitle(" ⚠️ Threat Analysis ")
	mv.ThreatList.SetBorder(true).SetTitle(" 🛡️ High-Severity Threats ")

	mv.ProcessTree.SetChangedFunc(func(node *tview.TreeNode) {
		if s.IsLocked() {
			return
		}
		if ref, ok := node.GetReference().(int32); ok {
			RenderEnhancedProcessDetails(mv, s, ref)
		}
	})

	mv.Search.SetChangedFunc(func(text string) {
		s.SetSearchQuery(text)
		if searchTimer != nil {
			searchTimer.Stop()
		}
		searchTimer = time.AfterFunc(250*time.Millisecond, func() {
			app.QueueUpdateDraw(func() { DrawProcessTree(mv.ProcessTree, s) })
		})
	})

	mv.ClearSearchButton.SetSelectedFunc(func() {
		if searchTimer != nil {
			searchTimer.Stop()
			searchTimer = nil
		}
		mv.Search.SetText("")
		s.SetSearchQuery("")
		go func() {
			time.Sleep(50 * time.Millisecond)
			app.QueueUpdateDraw(func() {
				DrawProcessTree(mv.ProcessTree, s)
				app.SetFocus(mv.Search)
			})
		}()
	})

	mv.SearchModeSelector.SetSelectedFunc(func(text string, index int) {
		modes := []string{"all", "name", "pid"}
		if index < len(modes) {
			s.SetSearchMode(modes[index])
		}
		app.QueueUpdateDraw(func() { DrawProcessTree(mv.ProcessTree, s) })
	})

	mv.FreezeButton.SetSelectedFunc(func() {
		if s.IsLocked() {
			s.UnlockPID()
			mv.DetailBox.SetTitle(" 🔬 Process Analysis ")
			mv.FreezeButton.SetLabel("Freeze 🥶")
		} else {
			if node := mv.ProcessTree.GetCurrentNode(); node != nil {
				if pid, ok := node.GetReference().(int32); ok {
					s.LockPID(pid)
					mv.DetailBox.SetTitle(" 🔬 Process Analysis [🔒 Frozen] ")
					mv.FreezeButton.SetLabel("Unfreeze 🫠")
					RenderEnhancedProcessDetails(mv, s, pid)
				}
			}
		}
	})

	searchBox := tview.NewFlex().AddItem(mv.Search, 0, 3, false).AddItem(mv.ClearSearchButton, 3, 0, false).AddItem(mv.SearchModeSelector, 0, 1, false)
	searchBox.SetBorder(true).SetBorderColor(theme.WarningColor)
	buttonPanel := tview.NewFlex().SetDirection(tview.FlexRow).AddItem(mv.HelpButton, 0, 1, false).AddItem(mv.AboutButton, 0, 1, false)
	headerFlex := tview.NewFlex().AddItem(mv.SystemInfo, 0, 2, false).AddItem(searchBox, 0, 3, false).AddItem(mv.ThreatPanel, 0, 2, false).AddItem(buttonPanel, 12, 1, false)
	detailFlex := tview.NewFlex().SetDirection(tview.FlexRow).AddItem(mv.FreezeButton, 1, 0, false).AddItem(mv.DetailBox, 0, 1, false)
	mainFlex := tview.NewFlex().AddItem(mv.ProcessTree, 0, 3, true).AddItem(mv.ThreatList, 0, 2, false).AddItem(detailFlex, 0, 2, false)
	mv.Grid = tview.NewGrid().SetRows(4, 0).SetColumns(0).AddItem(headerFlex, 0, 0, 1, 1, 0, 0, false).AddItem(mainFlex, 1, 0, 1, 1, 0, 0, true)

	helpModalContent := tview.NewTextView().SetDynamicColors(true).SetText(fmt.Sprintf(
		`[#%06x::b]🚀 HELP[-:-:-]
[#%06x]
 • [#%06x]Tab/Shift+Tab[-]: Navigate
 • [#%06x]F5[-]:             Refresh list
 • [#%06x]Ctrl+C[-]:        Quit

[#%06x]Click the 'Help' button again to close.[-]`,
		theme.TitleColor.Hex(), theme.FocusColor.Hex(), theme.WarningColor.Hex(), theme.WarningColor.Hex(), theme.WarningColor.Hex(), theme.SubtleTextColor.Hex()))
	helpModalContent.SetBorder(true).SetTitle(" 📖 Help ").SetBorderColor(theme.FocusColor)

	aboutContentFlex := tview.NewFlex().SetDirection(tview.FlexRow).
		AddItem(tview.NewTextView().SetDynamicColors(true).SetText(fmt.Sprintf("[#%06x::b]🚀 Enhanced Process Monitor[-:-:-]", theme.TitleColor.Hex())), 1, 0, false).
		AddItem(tview.NewTextView().SetText("A modern tool for real-time process monitoring."), 2, 0, false).
		AddItem(tview.NewTextView().SetDynamicColors(true).SetText(fmt.Sprintf("\n[#%06x::b]Creator:[-:-:-]", theme.FocusColor.Hex())), 2, 0, false)

	ghLink := "https://github.com/Null-Err0r"
	ghButton := tview.NewButton("Open 🌐").SetStyle(tcell.StyleDefault.Background(theme.ButtonBgColor).Foreground(theme.FocusColor))
	ghButton.SetSelectedFunc(func() { openURL(ghLink) })
	githubFlex := tview.NewFlex().SetDirection(tview.FlexColumn).
		AddItem(tview.NewTextView().SetText(" • GitHub:"), 11, 0, false).
		AddItem(tview.NewTextView().SetDynamicColors(true).SetText(fmt.Sprintf("[#%06x]%s[-]", theme.NetworkColor.Hex(), ghLink)), 0, 1, false).
		AddItem(ghButton, 12, 0, true)
	aboutContentFlex.AddItem(githubFlex, 1, 0, true)

	tgLink := "https://t.me/NullError_ir"
	tgButton := tview.NewButton("Open 🌐").SetStyle(tcell.StyleDefault.Background(theme.ButtonBgColor).Foreground(theme.FocusColor))
	tgButton.SetSelectedFunc(func() { openURL(tgLink) })
	telegramFlex := tview.NewFlex().SetDirection(tview.FlexColumn).
		AddItem(tview.NewTextView().SetText(" • Telegram:"), 11, 0, false).
		AddItem(tview.NewTextView().SetDynamicColors(true).SetText(fmt.Sprintf("[#%06x]%s[-]", theme.NetworkColor.Hex(), tgLink)), 0, 1, false).
		AddItem(tgButton, 12, 0, true)
	aboutContentFlex.AddItem(telegramFlex, 1, 0, true)

	aboutContentFlex.AddItem(tview.NewTextView().SetDynamicColors(true).SetText(fmt.Sprintf("\n[#%06x]Click 'About' again or press Esc to close.[-]", theme.SubtleTextColor.Hex())), 2, 0, false)
	aboutContentFlex.SetBorder(true).SetTitle(" ✨ About ").SetBorderColor(theme.FocusColor)

	mv.Pages.AddPage("main", mv.Grid, true, true)
	mv.Pages.AddPage("help", createModal(helpModalContent, 40, 9), true, false)
	mv.Pages.AddPage("about", createModal(aboutContentFlex, 70, 9), true, false)

	var helpVisible, aboutVisible bool
	mv.HelpButton.SetSelectedFunc(func() {
		if helpVisible {
			mv.Pages.HidePage("help")
			app.SetFocus(mv.ProcessTree)
		} else {
			if aboutVisible {
				mv.Pages.HidePage("about")
				aboutVisible = false
			}
			mv.Pages.ShowPage("help")
			app.SetFocus(mv.Pages)
		}
		helpVisible = !helpVisible
	})
	mv.AboutButton.SetSelectedFunc(func() {
		if aboutVisible {
			mv.Pages.HidePage("about")
			app.SetFocus(mv.ProcessTree)
		} else {
			if helpVisible {
				mv.Pages.HidePage("help")
				helpVisible = false
			}
			mv.Pages.ShowPage("about")
			app.SetFocus(mv.Pages.GetPage("about")) 
		}
		aboutVisible = !aboutVisible
	})
	return mv
}

func DrawProcessTree(tree *tview.TreeView, s *AppState) {
	var selectedPID int32 = -1
	if node := tree.GetCurrentNode(); node != nil {
		if pid, ok := node.GetReference().(int32); ok {
			selectedPID = pid
		}
	}
	s.RLock()
	defer s.RUnlock()
	root := tree.GetRoot()
	root.ClearChildren()
	filteredProcs := make(map[int32]*ProcessInfo)
	if s.SearchQuery != "" {
		for _, pInfo := range s.AllProcs {
			if matchesAdvancedFilter(pInfo, s.SearchQuery, s.SearchMode) {
				curr := pInfo
				for curr != nil {
					if _, exists := filteredProcs[curr.Process.Pid]; !exists {
						filteredProcs[curr.Process.Pid] = curr
					}
					curr = curr.ParentInfo
				}
			}
		}
	}
	var rootPIDsToDraw []int32
	var procsToDraw map[int32]*ProcessInfo
	if s.SearchQuery != "" {
		procsToDraw = filteredProcs
		for pid, pInfo := range procsToDraw {
			if pInfo.Ppid == 0 || procsToDraw[pInfo.Ppid] == nil {
				rootPIDsToDraw = append(rootPIDsToDraw, pid)
			}
		}
	} else {
		procsToDraw = s.AllProcs
		rootPIDsToDraw = s.RootPIDs
	}
	sortPIDs(rootPIDsToDraw, s)
	for _, pid := range rootPIDsToDraw {
		if pInfo, ok := procsToDraw[pid]; ok {
			node := createEnhancedProcessNode(pInfo, s)
			root.AddChild(node)
			addChildrenRecursive(node, pInfo, s, procsToDraw)
		}
	}
	if newNode := findNodeByPID(root, selectedPID); newNode != nil {
		tree.SetCurrentNode(newNode)
	} else if len(root.GetChildren()) > 0 {
		tree.SetCurrentNode(root.GetChildren()[0])
	}
}

func DrawThreatList(mv *MainView, s *AppState) {
	s.RLock()
	defer s.RUnlock()

	var threats []string
	var pids []int32
	for pid := range s.AllProcs {
		pids = append(pids, pid)
	}
	sort.Slice(pids, func(i, j int) bool { return pids[i] < pids[j] })

	for _, pid := range pids {
		if pInfo, ok := s.AllProcs[pid]; ok {
			if rule := s.RulesEngine.Evaluate(pInfo, pInfo.ParentInfo); rule != nil {
				if rule.Severity == "High" || rule.Severity == "Critical" {
					color, prefix := getNodeStyle(pInfo, rule)
					threats = append(threats, fmt.Sprintf("[#%06x]%s[%d] %s - %s[-]", color.Hex(), prefix, pInfo.Process.Pid, pInfo.Name, rule.Name))
				}
			}
		}
	}

	if len(threats) > 0 {
		mv.ThreatList.SetText(strings.Join(threats, "\n"))
	} else {
		mv.ThreatList.SetText(fmt.Sprintf("\n\n\nNo high-severity threats detected.[-]", theme.SafeColor.Hex()))
	}
	mv.ThreatList.ScrollToBeginning()
}

func addChildrenRecursive(node *tview.TreeNode, pInfo *ProcessInfo, s *AppState, procsToDraw map[int32]*ProcessInfo) {
	var childPIDs []int32
	for _, child := range pInfo.Children {
		if _, ok := procsToDraw[child.Process.Pid]; ok {
			childPIDs = append(childPIDs, child.Process.Pid)
		}
	}
	sortPIDs(childPIDs, s)
	for _, pid := range childPIDs {
		childInfo := procsToDraw[pid]
		childNode := createEnhancedProcessNode(childInfo, s)
		node.AddChild(childNode)
		addChildrenRecursive(childNode, childInfo, s, procsToDraw)
	}
}

func createEnhancedProcessNode(pInfo *ProcessInfo, s *AppState) *tview.TreeNode {
	s.RLock()
	parentInfo := pInfo.ParentInfo
	searchQuery := s.SearchQuery
	s.RUnlock()
	matchedRule := s.RulesEngine.Evaluate(pInfo, parentInfo)
	color, prefix := getNodeStyle(pInfo, matchedRule)
	branchSymbol := ""
	if pInfo.Level > 0 {
		branchSymbol = "└─ "
	}
	nodeText := fmt.Sprintf("%s%s%s[%d] %s (%s)", strings.Repeat("  ", pInfo.Level), branchSymbol, prefix, pInfo.Process.Pid, pInfo.Name, pInfo.Username)
	if matchedRule != nil {
		nodeText += fmt.Sprintf(" ⚠️ %s", matchedRule.Name)
	}
	node := tview.NewTreeNode(nodeText).SetReference(pInfo.Process.Pid).SetSelectable(true).SetColor(color).SetExpanded(pInfo.Level < 2 || searchQuery != "")
	return node
}

func getNodeStyle(pInfo *ProcessInfo, rule *Rule) (tcell.Color, string) {
	if rule != nil {
		switch rule.Severity {
		case "Critical":
			return theme.CriticalColor, "🚨 "
		case "High":
			return theme.DangerColor, "⚠️ "
		case "Medium":
			return theme.WarningColor, "⚡ "
		}
	}
	if pInfo.IsDeleted {
		return theme.DeletedColor, "👻 "
	}
	if len(pInfo.NetCons) > 0 {
		return theme.NetworkColor, "🌐 "
	}
	return theme.SafeColor, "✅ "
}

func RenderEnhancedProcessDetails(mv *MainView, s *AppState, pid int32) {
	s.RLock()
	pInfo, ok := s.AllProcs[pid]
	publicIP := s.PublicIP
	s.RUnlock()
	if !ok {
		mv.DetailBox.SetText(fmt.Sprintf("[#%06x]❌ Process not found", theme.DangerColor.Hex()))
		return
	}

	if pInfo.NetCons == nil {
		connections, err := pInfo.Process.Connections()
		if err == nil {
			pInfo.NetCons = connections
		} else {
			pInfo.NetCons = []psnet.ConnectionStat{}
		}
	}

	var b strings.Builder
	fmt.Fprintf(&b, "[#%06x::b]🔍 PROCESS ANALYSIS[-:-:-]\n\n", theme.TitleColor.Hex())
	fmt.Fprintf(&b, "[#%06x::b]📋 BASIC INFO[-:-:-]\n[#%06x]━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━[-]\n", theme.FocusColor.Hex(), theme.SubtleTextColor.Hex())
	fmt.Fprintf(&b, "[#%06x]PID:[-] %d\n[#%06x]Name:[-] %s\n[#%06x]User:[-] %s\n", theme.TitleColor.Hex(), pInfo.Process.Pid, theme.TitleColor.Hex(), pInfo.Name, theme.TitleColor.Hex(), pInfo.Username)
	if pInfo.CreateTime > 0 {
		fmt.Fprintf(&b, "[#%06x]Started:[-] %s\n\n", theme.TitleColor.Hex(), time.Unix(pInfo.CreateTime/1000, 0).Format("2006-01-02 15:04:05"))
	}
	fmt.Fprintf(&b, "[#%06x::b]⚡ RESOURCE USAGE[-:-:-]\n[#%06x]━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━[-]\n", theme.FocusColor.Hex(), theme.SubtleTextColor.Hex())
	fmt.Fprintf(&b, "[#%06x]CPU:[-] %.2f%% %s\n", theme.TitleColor.Hex(), pInfo.CPU, createProgressBar(int(pInfo.CPU)))
	fmt.Fprintf(&b, "[#%06x]Memory:[-] %.2f%% %s\n\n", theme.TitleColor.Hex(), pInfo.Mem, createProgressBar(int(pInfo.Mem)))

	if len(pInfo.NetCons) > 0 {
		fmt.Fprintf(&b, "[#%06x::b]🌐 NETWORK CONNECTIONS (%d)[-:-:-]\n[#%06x]━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━[-]\n", theme.FocusColor.Hex(), len(pInfo.NetCons), theme.SubtleTextColor.Hex())
		if publicIP != "Fetching..." {
			fmt.Fprintf(&b, "[#%06x]Your Public IP:[-] [#%06x::b]%s[-:-]\n\n", theme.TitleColor.Hex(), theme.PrimaryTextColor.Hex(), publicIP)
		}
		for i, conn := range pInfo.NetCons {
			fmt.Fprintf(&b, "[#%06x]Conn %d:[-] [#%06x]%s[-]\n", theme.TitleColor.Hex(), i+1, getStatusColor(conn.Status).Hex(), conn.Status)
			fmt.Fprintf(&b, "  [#%06x]Local:[-] %s:%d\n", theme.NetworkColor.Hex(), conn.Laddr.IP, conn.Laddr.Port)
			if conn.Raddr.IP != "" {
				fmt.Fprintf(&b, "  [#%06x]Remote:[-] %s:%d\n", theme.NetworkColor.Hex(), conn.Raddr.IP, conn.Raddr.Port)
			}
		}
	}
	mv.DetailBox.SetText(b.String()).ScrollToBeginning()
}

func createProgressBar(percent int) string {
	width := 20
	color := theme.SafeColor
	if percent > 100 {
		percent = 100
	} else if percent < 0 {
		percent = 0
	}
	filled := (percent * width) / 100
	bar := "[" + strings.Repeat("█", filled) + strings.Repeat("░", width-filled) + "]"
	if percent > 80 {
		color = theme.DangerColor
	} else if percent > 60 {
		color = theme.WarningColor
	}
	return fmt.Sprintf("[#%06x]%s[-]", color.Hex(), bar)
}

func getStatusColor(status string) tcell.Color {
	switch status {
	case "LISTEN":
		return theme.FocusColor
	case "ESTABLISHED":
		return theme.SafeColor
	default:
		return theme.WarningColor
	}
}

func ResolveIP(ip string) (string, bool) {
	dnsMutex.Lock()
	hostname, found := dnsCache[ip]
	dnsMutex.Unlock()
	if found {
		return hostname, hostname != ip
	}
	go func() {
		names, err := net.LookupAddr(ip)
		hostname := ip
		if err == nil && len(names) > 0 {
			hostname = strings.TrimSuffix(names[0], ".")
		}
		dnsMutex.Lock()
		dnsCache[ip] = hostname
		dnsMutex.Unlock()
	}()
	return ip, false
}

func (s *AppState) LockPID(pid int32)      { s.Lock(); s.lockedPID = pid; s.Unlock() }
func (s *AppState) UnlockPID()             { s.Lock(); s.lockedPID = 0; s.Unlock() }
func (s *AppState) IsLocked() bool         { s.RLock(); defer s.RUnlock(); return s.lockedPID != 0 }
func (s *AppState) GetLock() (int32, bool) { s.RLock(); defer s.RUnlock(); return s.lockedPID, s.lockedPID != 0 }
func (s *AppState) SetSearchQuery(query string) {
	s.Lock()
	s.SearchQuery = strings.ToLower(strings.TrimSpace(query))
	s.Unlock()
}
func (s *AppState) SetSearchMode(mode string) { s.Lock(); s.SearchMode = mode; s.Unlock() }

func UpdateEnhancedSummary(mv *MainView, s *AppState) {
	_, _, uptime, host, processCount := GetSystemSummary()
	mv.SystemInfo.SetText(fmt.Sprintf("[#%06x]Host:[-][#%06x]%s[-]\n[#%06x]Uptime:[-][#%06x]%s[-]\n[#%06x]Processes:[-][#%06x]%d[-]",
		theme.TitleColor.Hex(), theme.PrimaryTextColor.Hex(), host, theme.TitleColor.Hex(), theme.PrimaryTextColor.Hex(), uptime, theme.TitleColor.Hex(), theme.PrimaryTextColor.Hex(), processCount))
	s.RLock()
	highThreatCount := 0
	for _, pInfo := range s.AllProcs {
		if rule := s.RulesEngine.Evaluate(pInfo, pInfo.ParentInfo); rule != nil {
			if rule.Severity == "Critical" || rule.Severity == "High" {
				highThreatCount++
			}
		}
	}
	s.RUnlock()
	threatStatus := fmt.Sprintf("[#%06x]SECURE[-]", theme.SafeColor.Hex())
	if highThreatCount > 0 {
		threatStatus = fmt.Sprintf("[#%06x]%d HIGH THREATS[-]", theme.DangerColor.Hex(), highThreatCount)
	}
	mv.ThreatPanel.SetText(fmt.Sprintf("[#%06x]Status:[-]\n%s", theme.TitleColor.Hex(), threatStatus))
}

func sortPIDs(pids []int32, s *AppState) {
	sort.Slice(pids, func(i, j int) bool {
		s.RLock()
		defer s.RUnlock()
		p1, ok1 := s.AllProcs[pids[i]]
		p2, ok2 := s.AllProcs[pids[j]]
		if !ok1 || !ok2 {
			return false
		}
		var res bool
		switch s.SortBy {
		case "cpu":
			res = p1.CPU > p2.CPU
		case "mem":
			res = p1.Mem > p2.Mem
		case "pid":
			res = p1.Process.Pid < p2.Process.Pid
		case "name":
			res = strings.ToLower(p1.Name) < strings.ToLower(p2.Name)
		default:
			res = p1.CPU > p2.CPU
		}
		if s.SortAsc {
			return !res
		}
		return res
	})
}

func findNodeByPID(root *tview.TreeNode, pid int32) *tview.TreeNode {
	if root.GetReference() != nil {
		if refPID, ok := root.GetReference().(int32); ok && refPID == pid {
			return root
		}
	}
	for _, child := range root.GetChildren() {
		if found := findNodeByPID(child, pid); found != nil {
			return found
		}
	}
	return nil
}

func SetupEnhancedInputCapture(application *tview.Application, s *AppState, mv *MainView) {
	focusElements := []tview.Primitive{mv.ProcessTree, mv.Search, mv.ClearSearchButton, mv.SearchModeSelector, mv.FreezeButton, mv.HelpButton, mv.AboutButton}
	currentFocus := 0
	application.SetInputCapture(func(event *tcell.EventKey) *tcell.EventKey {
		if name, _ := mv.Pages.GetFrontPage(); name != "main" {
			return event
		}
		switch event.Key() {
		case tcell.KeyTab:
			currentFocus = (currentFocus + 1) % len(focusElements)
			application.SetFocus(focusElements[currentFocus])
			return nil
		case tcell.KeyBacktab:
			currentFocus = (currentFocus - 1 + len(focusElements)) % len(focusElements)
			application.SetFocus(focusElements[currentFocus])
			return nil
		case tcell.KeyCtrlC:
			application.Stop()
			return nil
		case tcell.KeyEnter:
			return event
		case tcell.KeyF5:
			go UpdateProcessSnapshot(s)
			return nil
		case tcell.KeyEscape:
			if mv.Search.GetText() != "" {
				mv.Search.SetText("")
			}
			return nil
		}
		return event
	})
}

func main() {
	appState := NewState()
	appState.RulesEngine = NewRulesEngine()
	app = tview.NewApplication().EnableMouse(true)
	mainView := NewMainView(app, appState)
	SetupEnhancedInputCapture(app, appState, mainView)

	go UpdateProcessSnapshot(appState)
	go updatePublicIP(appState)
	app.SetFocus(mainView.ProcessTree)

	go func() {
		ticker := time.NewTicker(3 * time.Second)
		defer ticker.Stop()
		for {
			<-ticker.C
			go UpdateProcessSnapshot(appState)

			app.QueueUpdateDraw(func() {
				if app.GetFocus() != mainView.Search {
					DrawProcessTree(mainView.ProcessTree, appState)
				}
				DrawThreatList(mainView, appState)
				if _, locked := appState.GetLock(); !locked {
					if node := mainView.ProcessTree.GetCurrentNode(); node != nil {
						if ref, ok := node.GetReference().(int32); ok {
							RenderEnhancedProcessDetails(mainView, appState, ref)
						}
					}
				}
			})
		}
	}()

	go func() {
		ticker := time.NewTicker(2 * time.Second)
		defer ticker.Stop()
		for {
			<-ticker.C
			app.QueueUpdateDraw(func() {
				UpdateEnhancedSummary(mainView, appState)
			})
		}
	}()

	if err := app.SetRoot(mainView.Pages, true).Run(); err != nil {
		fmt.Fprintf(os.Stderr, "❌ Error: %v\n", err)
		os.Exit(1)
	}
}
