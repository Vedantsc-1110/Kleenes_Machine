import tkinter as tk
from tkinter import messagebox, font
import math
from collections import deque, defaultdict

# ==========================================
# PART 1: AUTOMATA LOGIC & DATA STRUCTURES
# ==========================================

class State:
    _id_counter = 0

    def __init__(self, label=None, is_final=False):
        self.id = State._id_counter
        State._id_counter += 1
        self.label = label if label else f"q{self.id}"
        self.is_final = is_final
        self.transitions = defaultdict(list)  # char -> list of State objects

    def add_transition(self, char, state):
        self.transitions[char].append(state)

    def __repr__(self):
        return self.label

class NFA:
    def __init__(self, start, end):
        self.start = start
        self.end = end  # Thomson construction usually produces one final state initially

    def get_all_states(self):
        """BFS to get all reachable states."""
        visited = set()
        queue = deque([self.start])
        states = []
        while queue:
            s = queue.popleft()
            if s not in visited:
                visited.add(s)
                states.append(s)
                for char, neighbors in s.transitions.items():
                    for n in neighbors:
                        queue.append(n)
        return states

class DFA:
    def __init__(self, start_state, states, alphabet):
        self.start = start_state
        self.states = states
        self.alphabet = alphabet
        self.current_state = start_state

    def reset(self):
        self.current_state = self.start

    def step(self, char):
        if char in self.current_state.transitions:
            # DFA has exactly one transition per char (or goes to trap, implicit here)
            next_state = self.current_state.transitions[char][0]
            self.current_state = next_state
            return True
        return False

    def is_accepting(self):
        return self.current_state.is_final

# ==========================================
# PART 2: REGEX PARSING & CONVERSION ALGORITHMS
# ==========================================

class RegexProcessor:
    def __init__(self):
        self.precedence = {'*': 3, '.': 2, '|': 1, '(': 0}

    def _insert_explicit_concat(self, regex):
        """Inserts '.' for explicit concatenation."""
        res = ""
        for i in range(len(regex)):
            c1 = regex[i]
            res += c1
            if i + 1 < len(regex):
                c2 = regex[i+1]
                # Scenarios where we add dot:
                # char-char (ab), char-( (a(), *-char (*a), *-( (*()
                if (c1.isalnum() or c1 == '*' or c1 == ')') and (c2.isalnum() or c2 == '('):
                    res += '.'
        return res

    def _to_postfix(self, regex):
        """Shunting-yard algorithm to convert infix regex to postfix."""
        output = []
        stack = []
        
        for char in regex:
            if char.isalnum():  # Operand
                output.append(char)
            elif char == '(':
                stack.append(char)
            elif char == ')':
                while stack and stack[-1] != '(':
                    output.append(stack.pop())
                stack.pop() # Pop '('
            elif char in self.precedence:
                while stack and stack[-1] != '(' and self.precedence.get(stack[-1], 0) >= self.precedence[char]:
                    output.append(stack.pop())
                stack.append(char)
        
        while stack:
            output.append(stack.pop())
        
        return "".join(output)

    def regex_to_nfa(self, regex_str):
        """Thomson's Construction Algorithm."""
        if not regex_str:
            return None
            
        formatted_regex = self._insert_explicit_concat(regex_str)
        postfix = self._to_postfix(formatted_regex)
        stack = []

        State._id_counter = 0 # Reset IDs for clean visualization

        for char in postfix:
            if char.isalnum(): # Basic symbol
                start = State()
                end = State()
                start.add_transition(char, end)
                stack.append(NFA(start, end))
            
            elif char == '.': # Concatenation
                if len(stack) < 2: return None
                n2 = stack.pop()
                n1 = stack.pop()
                # Connect n1 end to n2 start with epsilon
                n1.end.add_transition('ε', n2.start)
                n1.end.is_final = False # n1 end is no longer final
                stack.append(NFA(n1.start, n2.end))
            
            elif char == '|': # Union
                if len(stack) < 2: return None
                n2 = stack.pop()
                n1 = stack.pop()
                start = State()
                end = State()
                
                # Split from new start
                start.add_transition('ε', n1.start)
                start.add_transition('ε', n2.start)
                
                # Converge to new end
                n1.end.add_transition('ε', end)
                n2.end.add_transition('ε', end)
                
                n1.end.is_final = False
                n2.end.is_final = False
                stack.append(NFA(start, end))
                
            elif char == '*': # Kleene Star
                if not stack: return None
                n = stack.pop()
                start = State()
                end = State()
                
                start.add_transition('ε', n.start)
                start.add_transition('ε', end) # Skip
                
                n.end.add_transition('ε', n.start) # Loop back
                n.end.add_transition('ε', end) # Exit
                
                n.end.is_final = False
                stack.append(NFA(start, end))
        
        if not stack: return None
        result_nfa = stack.pop()
        result_nfa.end.is_final = True
        return result_nfa

    def nfa_to_dfa(self, nfa):
        """Subset Construction Algorithm."""
        if not nfa: return None
        
        # Helper: Epsilon Closure
        def get_epsilon_closure(states):
            stack = list(states)
            closure = set(states)
            while stack:
                s = stack.pop()
                if 'ε' in s.transitions:
                    for next_s in s.transitions['ε']:
                        if next_s not in closure:
                            closure.add(next_s)
                            stack.append(next_s)
            return frozenset(closure)

        # Helper: Move
        def move(states, char):
            res = set()
            for s in states:
                if char in s.transitions:
                    for next_s in s.transitions[char]:
                        res.add(next_s)
            return res

        # 1. Determine Alphabet
        all_nfa_states = nfa.get_all_states()
        alphabet = set()
        for s in all_nfa_states:
            for char in s.transitions:
                if char != 'ε':
                    alphabet.add(char)
        alphabet = sorted(list(alphabet))

        # 2. Initial State
        initial_closure = get_epsilon_closure([nfa.start])
        
        # Mapping frozenset(states) -> DFA State object
        dfa_states_map = {}
        unprocessed = deque([initial_closure])
        
        # Create DFA start state
        start_node = State(label="S0", is_final=any(s.is_final for s in initial_closure))
        dfa_states_map[initial_closure] = start_node
        
        State._id_counter = 0 # Reset for DFA naming
        dfa_state_counter = 1

        while unprocessed:
            current_set = unprocessed.popleft()
            current_dfa_state = dfa_states_map[current_set]
            
            for char in alphabet:
                next_set = get_epsilon_closure(move(current_set, char))
                
                if not next_set:
                    continue # Dead state usually ignored in visuals or implicit
                
                if next_set not in dfa_states_map:
                    is_final = any(s.is_final for s in next_set)
                    new_state = State(label=f"S{dfa_state_counter}", is_final=is_final)
                    dfa_state_counter += 1
                    dfa_states_map[next_set] = new_state
                    unprocessed.append(next_set)
                
                current_dfa_state.add_transition(char, dfa_states_map[next_set])
        
        return DFA(start_node, list(dfa_states_map.values()), alphabet)


# ==========================================
# PART 3: VISUALIZATION ENGINE (Tkinter)
# ==========================================

class AutomataCanvas(tk.Canvas):
    def __init__(self, master, **kwargs):
        super().__init__(master, **kwargs)
        self.configure(bg="#f0f0f0")
        self.node_radius = 20
        self.nodes_pos = {} # State obj -> (x, y)

    def _calculate_layout(self, start_node, all_states):
        """
        Simple level-based layout algorithm.
        BFS to determine depth, then distribute vertically.
        """
        levels = defaultdict(list)
        visited = {start_node}
        queue = deque([(start_node, 0)])
        levels[0].append(start_node)
        
        max_depth = 0
        
        # BFS for levels
        while queue:
            curr, depth = queue.popleft()
            max_depth = max(max_depth, depth)
            
            # Sort transitions to keep deterministic order
            sorted_trans = sorted(curr.transitions.items())
            for char, neighbors in sorted_trans:
                for n in neighbors:
                    if n not in visited:
                        visited.add(n)
                        levels[depth + 1].append(n)
                        queue.append((n, depth + 1))
        
        # Handle disconnected components (though unlikely in valid construction)
        for s in all_states:
            if s not in visited:
                levels[max_depth + 1].append(s)
                visited.add(s)

        # Assign coords
        width = self.winfo_width()
        height = self.winfo_height()
        
        # Margins
        margin_x = 60
        margin_y = 60
        
        if width < 100: width = 800
        if height < 100: height = 600

        col_width = (width - 2 * margin_x) / (len(levels) + 1 if len(levels) > 0 else 1)
        
        self.nodes_pos = {}
        
        for depth, states in levels.items():
            x = margin_x + depth * col_width * 1.5
            row_height = (height - 2 * margin_y) / (len(states) + 1)
            for idx, s in enumerate(states):
                y = margin_y + (idx + 1) * row_height
                self.nodes_pos[s] = (x, y)

    def draw_automaton(self, start_node, all_states):
        self.delete("all")
        self._calculate_layout(start_node, all_states)
        
        # Draw Transitions first (so they are under nodes)
        for s in all_states:
            x1, y1 = self.nodes_pos[s]
            
            # Group transitions by destination
            grouped_trans = defaultdict(list)
            for char, dests in s.transitions.items():
                for d in dests:
                    grouped_trans[d].append(char)
            
            for dest, chars in grouped_trans.items():
                x2, y2 = self.nodes_pos[dest]
                label = ",".join(chars)
                self._draw_edge(x1, y1, x2, y2, label, is_self_loop=(s == dest))

        # Draw Nodes
        for s in all_states:
            x, y = self.nodes_pos[s]
            self._draw_node(x, y, s.label, s.is_final, is_start=(s == start_node))

    def _draw_node(self, x, y, label, is_final, is_start):
        r = self.node_radius
        color = "#e1f5fe" if not is_start else "#ffe0b2"
        outline = "#01579b"
        
        # Start arrow
        if is_start:
            self.create_line(x - 50, y, x - r, y, arrow=tk.LAST, fill="#555", width=2)
            self.create_text(x - 60, y, text="Start", fill="#555")

        # Main circle
        self.create_oval(x-r, y-r, x+r, y+r, fill=color, outline=outline, width=2)
        
        # Inner circle for final state
        if is_final:
            self.create_oval(x-r+4, y-r+4, x+r-4, y+r-4, outline=outline, width=2)
            
        self.create_text(x, y, text=label, font=("Helvetica", 10, "bold"))

    def _draw_edge(self, x1, y1, x2, y2, label, is_self_loop=False):
        r = self.node_radius
        
        if is_self_loop:
            # Draw a loop above the node
            self.create_line(x1, y1-r, x1, y1-3*r, x1+2*r, y1-3*r, x1+r*0.8, y1-r*0.8, smooth=True, arrow=tk.LAST, fill="#424242")
            self.create_text(x1+r, y1-3.5*r, text=label)
        else:
            # Calculate angle for arrow trimming
            angle = math.atan2(y2 - y1, x2 - x1)
            
            # Trim line to stop at circle edge
            start_x = x1 + r * math.cos(angle)
            start_y = y1 + r * math.sin(angle)
            end_x = x2 - r * math.cos(angle)
            end_y = y2 - r * math.sin(angle)
            
            # Check for bidirectional edges to curve them
            # (Simple heuristic: if direct line, use straight, otherwise curve)
            # Here we just curve everything slightly to avoid overlap on reverse paths
            
            mid_x = (start_x + end_x) / 2
            mid_y = (start_y + end_y) / 2
            
            # Offset control point for curve
            offset = 20
            # Perpendicular vector
            cx = mid_x - offset * math.sin(angle)
            cy = mid_y + offset * math.cos(angle)
            
            self.create_line(start_x, start_y, cx, cy, end_x, end_y, smooth=True, arrow=tk.LAST, fill="#424242")
            
            # Label pos
            lx = mid_x - (offset + 10) * math.sin(angle)
            ly = mid_y + (offset + 10) * math.cos(angle)
            self.create_text(lx, ly, text=label)

# ==========================================
# PART 4: MAIN APPLICATION GUI
# ==========================================

class KleeneApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Kleene's Theorem Simulator")
        self.root.geometry("1000x700")
        
        self.regex_processor = RegexProcessor()
        self.current_nfa = None
        self.current_dfa = None
        
        self._setup_ui()

    def _setup_ui(self):
        # Header
        header_frame = tk.Frame(self.root, bg="#263238", pady=10)
        header_frame.pack(fill=tk.X)
        
        title = tk.Label(header_frame, text="Kleene's Machine: Regex → NFA → DFA", 
                         font=("Helvetica", 16, "bold"), bg="#263238", fg="white")
        title.pack()

        # Input Zone
        control_frame = tk.Frame(self.root, pady=10, padx=10, bg="#ECEFF1")
        control_frame.pack(fill=tk.X)
        
        tk.Label(control_frame, text="Regex:", bg="#ECEFF1", font=("Arial", 11)).pack(side=tk.LEFT)
        self.regex_entry = tk.Entry(control_frame, width=30, font=("Arial", 11))
        self.regex_entry.pack(side=tk.LEFT, padx=5)
        self.regex_entry.insert(0, "(a|b)*abb") # Default Example
        
        btn_style = {"bg": "#2196F3", "fg": "white", "font": ("Arial", 10, "bold"), "relief": tk.FLAT, "padx": 10}
        
        tk.Button(control_frame, text="1. Build NFA", command=self.build_nfa, **btn_style).pack(side=tk.LEFT, padx=5)
        tk.Button(control_frame, text="2. Convert to DFA", command=self.build_dfa, **btn_style).pack(side=tk.LEFT, padx=5)
        
        # Test String Zone
        tk.Label(control_frame, text=" |  Test String:", bg="#ECEFF1", font=("Arial", 11)).pack(side=tk.LEFT, padx=5)
        self.test_entry = tk.Entry(control_frame, width=15, font=("Arial", 11))
        self.test_entry.pack(side=tk.LEFT, padx=5)
        
        test_btn_style = btn_style.copy()
        test_btn_style["bg"] = "#4CAF50"
        tk.Button(control_frame, text="Check", command=self.check_string, **test_btn_style).pack(side=tk.LEFT, padx=5)
        
        self.result_lbl = tk.Label(control_frame, text="", bg="#ECEFF1", font=("Arial", 11, "bold"))
        self.result_lbl.pack(side=tk.LEFT, padx=10)

        # Canvas Area
        self.canvas = AutomataCanvas(self.root)
        self.canvas.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Info bar
        self.info_lbl = tk.Label(self.root, text="Enter a regex using ( ) * | and alphanumeric characters.", bd=1, relief=tk.SUNKEN, anchor=tk.W)
        self.info_lbl.pack(fill=tk.X)

    def build_nfa(self):
        regex = self.regex_entry.get().strip()
        if not regex:
            messagebox.showerror("Error", "Please enter a Regex.")
            return
        
        try:
            self.current_nfa = self.regex_processor.regex_to_nfa(regex)
            if not self.current_nfa:
                raise ValueError("Invalid Regex Construction")
            
            states = self.current_nfa.get_all_states()
            self.current_dfa = None # Invalidate old DFA
            self.canvas.draw_automaton(self.current_nfa.start, states)
            self.info_lbl.config(text=f"NFA Generated: {len(states)} states. Implicit concatenation '.' added internally.")
            self.result_lbl.config(text="")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to build NFA: {str(e)}")

    def build_dfa(self):
        if not self.current_nfa:
            messagebox.showwarning("Warning", "Build the NFA first!")
            return
            
        try:
            self.current_dfa = self.regex_processor.nfa_to_dfa(self.current_nfa)
            self.canvas.draw_automaton(self.current_dfa.start, self.current_dfa.states)
            self.info_lbl.config(text=f"DFA Generated: {len(self.current_dfa.states)} states (via Subset Construction).")
            self.result_lbl.config(text="")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to build DFA: {str(e)}")

    def check_string(self):
        test_str = self.test_entry.get().strip()
        
        if self.current_dfa:
            # Use DFA logic
            self.current_dfa.reset()
            valid = True
            for char in test_str:
                if not self.current_dfa.step(char):
                    valid = False
                    break
            
            is_accepted = valid and self.current_dfa.is_accepting()
            self._show_result(is_accepted)
            
        elif self.current_nfa:
            # Simple NFA Simulation (Recursive or Set based)
            # Using set based simulation here similar to subset construction on the fly
            current_states = {self.current_nfa.start}
            
            # Helper for epsilon closure
            def epsilon_expand(states):
                stack = list(states)
                closure = set(states)
                while stack:
                    s = stack.pop()
                    if 'ε' in s.transitions:
                        for n in s.transitions['ε']:
                            if n not in closure:
                                closure.add(n)
                                stack.append(n)
                return closure

            current_states = epsilon_expand(current_states)
            
            valid = True
            for char in test_str:
                next_states = set()
                for s in current_states:
                    if char in s.transitions:
                        next_states.update(s.transitions[char])
                
                if not next_states:
                    valid = False
                    break
                current_states = epsilon_expand(next_states)
            
            is_accepted = valid and any(s.is_final for s in current_states)
            self._show_result(is_accepted)
        else:
            messagebox.showwarning("Warning", "Please build an automaton first.")

    def _show_result(self, accepted):
        if accepted:
            self.result_lbl.config(text="ACCEPTED", fg="green")
        else:
            self.result_lbl.config(text="REJECTED", fg="red")

if __name__ == "__main__":
    root = tk.Tk()
    app = KleeneApp(root)
    root.mainloop()