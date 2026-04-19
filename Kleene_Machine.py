import tkinter as tk
from tkinter import messagebox, font, ttk
import math
from collections import deque, defaultdict


# PART 1: AUTOMATA LOGIC & DATA STRUCTURES


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
        self.end = end

    def get_all_states(self):
        """BFS to get all reachable states."""
        visited = set()
        queue = deque([self.start])
        states = []
        visited.add(self.start)
        states.append(self.start)
        
        while queue:
            s = queue.popleft()
            for char, neighbors in s.transitions.items():
                for n in neighbors:
                    if n not in visited:
                        visited.add(n)
                        states.append(n)
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
            next_state = self.current_state.transitions[char][0]
            self.current_state = next_state
            return True
        return False

    def is_accepting(self):
        return self.current_state.is_final

    def get_transition_table(self):
        """Returns data for the transition table."""
        # Rows: States, Cols: Alphabet
        # Data: list of dictionaries
        data = []
        # Sort states naturally (S0, S1, S2...)
        sorted_states = sorted(self.states, key=lambda s: int(s.label[1:]) if s.label[1:].isdigit() else s.label)
        
        for s in sorted_states:
            # Mark start and final states in the table
            marker = ""
            if s == self.start: marker += "->"
            if s.is_final: marker += "*"
            
            row = {"State": f"{marker}{s.label}"}
            for char in self.alphabet:
                if char in s.transitions:
                    dest = s.transitions[char][0]
                    row[char] = dest.label
                else:
                    row[char] = "-" # Trap/Dead state implicit
            data.append(row)
        return data

# PART 2: REGEX PARSING & CONVERSION ALGORITHMS

class RegexProcessor:
    def __init__(self):
        self.precedence = {'*': 3, '.': 2, '|': 1, '(': 0}

    def _insert_explicit_concat(self, regex):
        res = ""
        for i in range(len(regex)):
            c1 = regex[i]
            res += c1
            if i + 1 < len(regex):
                c2 = regex[i+1]
                if (c1.isalnum() or c1 == '*' or c1 == ')') and (c2.isalnum() or c2 == '('):
                    res += '.'
        return res

    def _to_postfix(self, regex):
        output = []
        stack = []
        for char in regex:
            if char.isalnum():
                output.append(char)
            elif char == '(':
                stack.append(char)
            elif char == ')':
                while stack and stack[-1] != '(':
                    output.append(stack.pop())
                stack.pop()
            elif char in self.precedence:
                while stack and stack[-1] != '(' and self.precedence.get(stack[-1], 0) >= self.precedence[char]:
                    output.append(stack.pop())
                stack.append(char)
        while stack:
            output.append(stack.pop())
        return "".join(output)

    def _build_partial_nfa(self, postfix_subset):
        """Builds NFA from a partial postfix string (for step visualization)."""
        stack = []
        State._id_counter = 0 # Reset for consistency
        
        for char in postfix_subset:
            if char.isalnum():
                start = State()
                end = State()
                start.add_transition(char, end)
                stack.append(NFA(start, end))
            elif char == '.':
                if len(stack) < 2: return stack, "Error: missing operands for '.'"
                n2 = stack.pop()
                n1 = stack.pop()
                n1.end.add_transition('ε', n2.start)
                n1.end.is_final = False
                stack.append(NFA(n1.start, n2.end))
            elif char == '|':
                if len(stack) < 2: return stack, "Error: missing operands for '|'"
                n2 = stack.pop()
                n1 = stack.pop()
                start = State()
                end = State()
                start.add_transition('ε', n1.start)
                start.add_transition('ε', n2.start)
                n1.end.add_transition('ε', end)
                n2.end.add_transition('ε', end)
                n1.end.is_final = False
                n2.end.is_final = False
                stack.append(NFA(start, end))
            elif char == '*':
                if not stack: return stack, "Error: missing operand for '*'"
                n = stack.pop()
                start = State()
                end = State()
                start.add_transition('ε', n.start)
                start.add_transition('ε', end)
                n.end.add_transition('ε', n.start)
                n.end.add_transition('ε', end)
                n.end.is_final = False
                stack.append(NFA(start, end))
        
        return stack, None

    def regex_to_nfa(self, regex_str):
        formatted_regex = self._insert_explicit_concat(regex_str)
        postfix = self._to_postfix(formatted_regex)
        stack, error = self._build_partial_nfa(postfix)
        
        if error or not stack:
            return None
        
        result_nfa = stack.pop()
        result_nfa.end.is_final = True
        return result_nfa

    def get_construction_history(self, regex_str):
        """Generates snapshots of the stack for each step."""
        formatted_regex = self._insert_explicit_concat(regex_str)
        postfix = self._to_postfix(formatted_regex)
        
        steps = []
        
        # Start immediately with the first character operation
        for i in range(1, len(postfix) + 1):
            partial_postfix = postfix[:i]
            current_char = postfix[i-1]
            
            # Re-run construction to get fresh state objects for this moment in time
            current_stack, err = self._build_partial_nfa(partial_postfix)
            
            desc = ""
            if current_char.isalnum():
                desc = f"Push basic NFA for '{current_char}'"
            elif current_char == '.':
                desc = "Pop 2, Concatenate, Push result"
            elif current_char == '|':
                desc = "Pop 2, Union, Push result"
            elif current_char == '*':
                desc = "Pop 1, Apply Kleene Star, Push result"

            steps.append({
                "char": current_char,
                "postfix": partial_postfix,
                "stack": current_stack,
                "description": desc
            })
            
        return steps

    def nfa_to_dfa(self, nfa):
        if not nfa: return None
        
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

        def move(states, char):
            res = set()
            for s in states:
                if char in s.transitions:
                    for next_s in s.transitions[char]:
                        res.add(next_s)
            return res

        all_nfa_states = nfa.get_all_states()
        alphabet = set()
        for s in all_nfa_states:
            for char in s.transitions:
                if char != 'ε':
                    alphabet.add(char)
        alphabet = sorted(list(alphabet))

        initial_closure = get_epsilon_closure([nfa.start])
        dfa_states_map = {}
        unprocessed = deque([initial_closure])
        
        start_node = State(label="S0", is_final=any(s.is_final for s in initial_closure))
        dfa_states_map[initial_closure] = start_node
        
        State._id_counter = 0
        dfa_state_counter = 1

        while unprocessed:
            current_set = unprocessed.popleft()
            current_dfa_state = dfa_states_map[current_set]
            
            for char in alphabet:
                next_set = get_epsilon_closure(move(current_set, char))
                if not next_set: continue
                
                if next_set not in dfa_states_map:
                    is_final = any(s.is_final for s in next_set)
                    new_state = State(label=f"S{dfa_state_counter}", is_final=is_final)
                    dfa_state_counter += 1
                    dfa_states_map[next_set] = new_state
                    unprocessed.append(next_set)
                
                current_dfa_state.add_transition(char, dfa_states_map[next_set])
        
        return DFA(start_node, list(dfa_states_map.values()), alphabet)

    def minimize_dfa(self, dfa):
        if not dfa:
            return None
        if not dfa.states:
            return dfa

        def state_sort_key(state):
            suffix = state.label[1:]
            return (0, int(suffix)) if suffix.isdigit() else (1, state.label)

        # Remove unreachable states before partitioning.
        reachable = set()
        queue = deque([dfa.start])
        reachable.add(dfa.start)
        while queue:
            curr = queue.popleft()
            for char in dfa.alphabet:
                if char in curr.transitions:
                    nxt = curr.transitions[char][0]
                    if nxt not in reachable:
                        reachable.add(nxt)
                        queue.append(nxt)

        final_states = {s for s in reachable if s.is_final}
        non_final_states = reachable - final_states

        partitions = []
        if final_states:
            partitions.append(final_states)
        if non_final_states:
            partitions.append(non_final_states)

        # Standard partition refinement.
        changed = True
        while changed:
            changed = False
            state_to_block = {}
            for idx, block in enumerate(partitions):
                for state in block:
                    state_to_block[state] = idx

            next_partitions = []
            for block in partitions:
                signatures = defaultdict(set)
                for state in block:
                    signature = []
                    for char in dfa.alphabet:
                        if char in state.transitions:
                            target = state.transitions[char][0]
                            signature.append(state_to_block[target])
                        else:
                            signature.append(-1)
                    signatures[tuple(signature)].add(state)

                if len(signatures) > 1:
                    changed = True
                next_partitions.extend(signatures.values())
            partitions = next_partitions

        # Start block first, then deterministic ordering by representative label.
        start_block = None
        for block in partitions:
            if dfa.start in block:
                start_block = block
                break
        ordered_blocks = []
        if start_block is not None:
            ordered_blocks.append(start_block)
        remaining_blocks = [b for b in partitions if b is not start_block]
        remaining_blocks.sort(key=lambda b: state_sort_key(min(b, key=state_sort_key)))
        ordered_blocks.extend(remaining_blocks)

        new_states = []
        block_to_new_state = {}
        old_to_new_state = {}

        for idx, block in enumerate(ordered_blocks):
            representative = min(block, key=state_sort_key)
            new_state = State(label=f"S{idx}", is_final=representative.is_final)
            new_states.append(new_state)
            block_to_new_state[frozenset(block)] = new_state
            for old_state in block:
                old_to_new_state[old_state] = new_state

        for block in ordered_blocks:
            representative = min(block, key=state_sort_key)
            src_new = old_to_new_state[representative]
            for char in dfa.alphabet:
                if char in representative.transitions:
                    dst_old = representative.transitions[char][0]
                    src_new.add_transition(char, old_to_new_state[dst_old])

        return DFA(old_to_new_state[dfa.start], new_states, dfa.alphabet)



# PART 3: VISUALIZATION ENGINE (Tkinter)


class AutomataCanvas(tk.Canvas):
    def __init__(self, master, **kwargs):
        super().__init__(master, **kwargs)
        self.configure(bg="#1a1a2e")
        self.node_radius = 20
        self.nodes_pos = {}
        self.zoom_factor = 1.0
        self.min_zoom = 0.5
        self.max_zoom = 2.5
        self._last_draw_mode = None
        self._last_payload = None

    def zoom_in(self):
        self._set_zoom(self.zoom_factor * 1.2)

    def zoom_out(self):
        self._set_zoom(self.zoom_factor / 1.2)

    def _set_zoom(self, new_zoom):
        clamped = max(self.min_zoom, min(self.max_zoom, new_zoom))
        if abs(clamped - self.zoom_factor) < 1e-9:
            return
        self.zoom_factor = clamped
        self._redraw_last()

    def _redraw_last(self):
        if self._last_draw_mode == "single" and self._last_payload:
            start_node, all_states = self._last_payload
            self.draw_automaton(start_node, all_states)
        elif self._last_draw_mode == "multiple" and self._last_payload is not None:
            self.draw_multiple_nfas(self._last_payload)

    def _get_nfa_layout(self, start_node, all_states, width, height, offset_x=0):
        """Calculates positions for a single NFA component."""
        levels = defaultdict(list)
        visited = {start_node}
        queue = deque([(start_node, 0)])
        levels[0].append(start_node)
        max_depth = 0
        
        while queue:
            curr, depth = queue.popleft()
            max_depth = max(max_depth, depth)
            sorted_trans = sorted(curr.transitions.items())
            for char, neighbors in sorted_trans:
                for n in neighbors:
                    if n not in visited:
                        visited.add(n)
                        levels[depth + 1].append(n)
                        queue.append((n, depth + 1))
        
        # Add stragglers
        for s in all_states:
            if s not in visited:
                levels[max_depth + 1].append(s)
                visited.add(s)

        # Layout parameters
        margin_y = int(40 * self.zoom_factor)
        col_width = int(80 * self.zoom_factor)
        
        local_pos = {}
        
        # Calculate bounding box width for this NFA
        total_cols = len(levels)
        if total_cols == 0: total_cols = 1
        nfa_width = total_cols * col_width + int(40 * self.zoom_factor)
        
        # Determine minimum height needed for nodes so they don't overlap
        max_nodes_in_col = 0
        for states in levels.values():
            max_nodes_in_col = max(max_nodes_in_col, len(states))
        
        min_needed_height = int(max_nodes_in_col * (60 * self.zoom_factor) + margin_y * 2)
        actual_height = max(height, min_needed_height)
        
        for depth, states in levels.items():
            x = offset_x + int(40 * self.zoom_factor) + depth * col_width
            row_height = (actual_height - 2 * margin_y) / (len(states) + 1)
            for idx, s in enumerate(states):
                y = margin_y + (idx + 1) * row_height
                local_pos[s] = (x, y)
                
        return local_pos, nfa_width

    def draw_automaton(self, start_node, all_states):
        """Legacy wrapper for single automaton drawing."""
        self._last_draw_mode = "single"
        self._last_payload = (start_node, all_states)
        self.delete("all")
        self.nodes_pos = {}
        # We pass width/height, but _get_nfa_layout uses its own width logic and enforces min height
        pos, _ = self._get_nfa_layout(start_node, all_states, self.winfo_width(), self.winfo_height())
        self.nodes_pos = pos
        self._draw_from_pos(all_states, start_node)
        self.configure(scrollregion=self.bbox("all"))

    def draw_multiple_nfas(self, nfa_list):
        """Draws multiple disconnected NFAs side-by-side (for stack viz)."""
        self._last_draw_mode = "multiple"
        self._last_payload = nfa_list
        self.delete("all")
        self.nodes_pos = {}
        
        current_offset_x = 0
        h = self.winfo_height()
        if h < 100: h = 500
        
        all_states_combined = []
        
        for nfa in nfa_list:
            states = nfa.get_all_states()
            all_states_combined.extend(states)
            pos, width = self._get_nfa_layout(nfa.start, states, 0, h, current_offset_x)
            self.nodes_pos.update(pos)
            current_offset_x += width
            
        # Draw everything using the combined positions
        start_nodes = {nfa.start for nfa in nfa_list}
        self._draw_from_pos(all_states_combined, start_nodes)
        self.configure(scrollregion=self.bbox("all"))

    def _draw_from_pos(self, all_states, start_nodes):
        # Handle single start node or set of start nodes
        if isinstance(start_nodes, State):
            start_nodes = {start_nodes}
            
        # Draw Transitions
        for s in all_states:
            if s not in self.nodes_pos: continue
            x1, y1 = self.nodes_pos[s]
            
            grouped_trans = defaultdict(list)
            for char, dests in s.transitions.items():
                for d in dests:
                    grouped_trans[d].append(char)
            
            for dest, chars in grouped_trans.items():
                if dest not in self.nodes_pos: continue
                x2, y2 = self.nodes_pos[dest]
                label = ",".join(chars)
                self._draw_edge(x1, y1, x2, y2, label, is_self_loop=(s == dest))

        # Draw Nodes
        for s in all_states:
            if s not in self.nodes_pos: continue
            x, y = self.nodes_pos[s]
            self._draw_node(x, y, s.label, s.is_final, is_start=(s in start_nodes))

    def _draw_node(self, x, y, label, is_final, is_start):
        r = self.node_radius * self.zoom_factor
        color = "#9c88ff" if not is_start else "#6c5ce7"  # Violet shades
        outline = "#a29bfe"  # Light violet outline
        font_size = max(8, int(10 * self.zoom_factor))
        
        if is_start:
            self.create_line(x - (40 * self.zoom_factor), y, x - r, y, arrow=tk.LAST, fill="white", width=2)

        self.create_oval(x-r, y-r, x+r, y+r, fill=color, outline=outline, width=2)
        if is_final:
            self.create_oval(x-r+4, y-r+4, x+r-4, y+r-4, outline=outline, width=2)
            
        self.create_text(x, y, text=label, font=("Helvetica", font_size, "bold"), fill="white")

    def _draw_edge(self, x1, y1, x2, y2, label, is_self_loop=False):
        r = self.node_radius * self.zoom_factor
        if is_self_loop:
            self.create_line(x1, y1-r, x1, y1-3*r, x1+2*r, y1-3*r, x1+r*0.8, y1-r*0.8, smooth=True, arrow=tk.LAST, fill="white")
            self.create_text(x1+r, y1-3.5*r, text=label, fill="white")
        else:
            angle = math.atan2(y2 - y1, x2 - x1)
            start_x = x1 + r * math.cos(angle)
            start_y = y1 + r * math.sin(angle)
            end_x = x2 - r * math.cos(angle)
            end_y = y2 - r * math.sin(angle)
            
            mid_x = (start_x + end_x) / 2
            mid_y = (start_y + end_y) / 2
            offset = 15 * self.zoom_factor
            cx = mid_x - offset * math.sin(angle)
            cy = mid_y + offset * math.cos(angle)
            
            self.create_line(start_x, start_y, cx, cy, end_x, end_y, smooth=True, arrow=tk.LAST, fill="white")
            
            lx = mid_x - (offset + 10) * math.sin(angle)
            ly = mid_y + (offset + 10) * math.cos(angle)
            self.create_text(lx, ly, text=label, fill="white")


# PART 4: MAIN APPLICATION GUI


class KleeneApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Kleene's Theorem Simulator")
        self.root.geometry("1100x750")
        self.root.configure(bg="#1e1e2e")  # Dark background
        
        # Set ttk style
        style = ttk.Style()
        style.theme_use('clam')  # Modern theme
        
        # Custom styles
        style.configure('TButton', font=('Arial', 10, 'bold'), padding=6)
        style.configure('Fun.TButton', background='#ff6b6b', foreground='white', borderwidth=0)
        style.map('Fun.TButton', background=[('active', '#ff5252')], foreground=[('active', 'white')])
        
        style.configure('Test.TButton', background='#4ecdc4', foreground='white')
        style.map('Test.TButton', background=[('active', '#45b7aa')], foreground=[('active', 'white')])
        
        style.configure('Treeview', background='#2d2d3a', foreground='white', fieldbackground='#2d2d3a')
        style.configure('Treeview.Heading', background='#ff6b6b', foreground='white')
        style.map('Treeview', background=[('selected', '#ff6b6b')])
        
        self.regex_processor = RegexProcessor()
        self.current_nfa = None
        self.current_dfa = None
        
        # Step visualization state
        self.step_history = []
        self.current_step_idx = 0
        
        self._setup_ui()

    def _setup_ui(self):
        # Header
        header_frame = tk.Frame(self.root, bg="#ff6b6b", pady=15)
        header_frame.pack(fill=tk.X)
        title = tk.Label(header_frame, text="🚀 Kleene's Machine: Regex → NFA → DFA 🚀", 
                         font=("Helvetica", 18, "bold"), bg="#ff6b6b", fg="white")
        title.pack()

        # Input Zone
        control_frame = tk.Frame(self.root, pady=15, padx=15, bg="#2d2d3a")
        control_frame.pack(fill=tk.X)
        
        tk.Label(control_frame, text="Regex:", bg="#2d2d3a", fg="white", font=("Arial", 12, "bold")).pack(side=tk.LEFT)
        self.regex_entry = tk.Entry(control_frame, width=20, font=("Arial", 11))
        self.regex_entry.pack(side=tk.LEFT, padx=5)
        self.regex_entry.insert(0, "(a|b)*abb")
        
        tk.Button(control_frame, text="1. Build NFA", command=self.build_nfa, bg="#ff6b6b", fg="white", font=("Arial", 10, "bold"), relief=tk.FLAT, padx=10).pack(side=tk.LEFT, padx=5)
        tk.Button(control_frame, text="Steps", command=self.start_nfa_steps, bg="#ff6b6b", fg="white", font=("Arial", 10, "bold"), relief=tk.FLAT, padx=10).pack(side=tk.LEFT, padx=2)
        
        tk.Button(control_frame, text="2. Convert DFA", command=self.build_dfa, bg="#ff6b6b", fg="white", font=("Arial", 10, "bold"), relief=tk.FLAT, padx=10).pack(side=tk.LEFT, padx=5)
        self.btn_table = tk.Button(control_frame, text="Table", command=self.show_dfa_table, state=tk.DISABLED, bg="#ff6b6b", fg="white", disabledforeground="white", font=("Arial", 10, "bold"), relief=tk.FLAT, padx=10)
        self.btn_table.pack(side=tk.LEFT, padx=2)
        
        # Test String Zone
        tk.Label(control_frame, text="| Test:", bg="#2d2d3a", fg="white", font=("Arial", 12, "bold")).pack(side=tk.LEFT, padx=5)
        self.test_entry = tk.Entry(control_frame, width=10, font=("Arial", 11))
        self.test_entry.pack(side=tk.LEFT, padx=5)
        
        tk.Button(control_frame, text="Check", command=self.check_string, bg="#4ecdc4", fg="white", font=("Arial", 10, "bold"), relief=tk.FLAT, padx=10).pack(side=tk.LEFT, padx=5)

        # Step Control Panel (Initially Hidden)
        self.step_frame = tk.Frame(self.root, bg="#ffeaa7", pady=10)
        # We pack this later when needed
        
        tk.Button(self.step_frame, text="<< Prev", command=self.prev_step, bg="#ff6b6b", fg="white", font=("Arial", 10, "bold"), relief=tk.FLAT, padx=10).pack(side=tk.LEFT, padx=20)
        self.step_lbl = tk.Label(self.step_frame, text="Step 0", bg="#ffeaa7", fg="black", font=("Arial", 12, "bold"), width=40)
        self.step_lbl.pack(side=tk.LEFT)
        tk.Button(self.step_frame, text="Next >>", command=self.next_step, bg="#ff6b6b", fg="white", font=("Arial", 10, "bold"), relief=tk.FLAT, padx=10).pack(side=tk.LEFT, padx=20)
        tk.Button(self.step_frame, text="Close Steps", command=self.close_steps, bg="#ff6b6b", fg="white", font=("Arial", 10, "bold"), relief=tk.FLAT, padx=10).pack(side=tk.RIGHT, padx=10)

        # Canvas Area with Scrollbars
        canvas_frame = tk.Frame(self.root)
        canvas_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        self.canvas = AutomataCanvas(canvas_frame)
        tk.Button(control_frame, text="Zoom +", command=self.canvas.zoom_in, bg="#a8e6cf", fg="black", font=("Arial", 10, "bold"), relief=tk.FLAT, padx=10).pack(side=tk.LEFT, padx=2)
        tk.Button(control_frame, text="Zoom -", command=self.canvas.zoom_out, bg="#a8e6cf", fg="black", font=("Arial", 10, "bold"), relief=tk.FLAT, padx=10).pack(side=tk.LEFT, padx=2)
        
        h_scroll = tk.Scrollbar(canvas_frame, orient=tk.HORIZONTAL, command=self.canvas.xview)
        v_scroll = tk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=self.canvas.yview)
        
        self.canvas.configure(xscrollcommand=h_scroll.set, yscrollcommand=v_scroll.set)
        
        h_scroll.pack(side=tk.BOTTOM, fill=tk.X)
        v_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        self.info_lbl = tk.Label(self.root, text="Ready.", bd=1, relief=tk.SUNKEN, anchor=tk.W, bg="#2d2d3a", fg="white")
        self.info_lbl.pack(fill=tk.X)

    def build_nfa(self):
        self.close_steps()
        regex = self.regex_entry.get().strip()
        if not regex: return
        try:
            self.current_nfa = self.regex_processor.regex_to_nfa(regex)
            if not self.current_nfa: raise ValueError("Invalid Regex")
            
            states = self.current_nfa.get_all_states()
            self.current_dfa = None
            self.btn_table.config(state=tk.DISABLED)
            
            self.canvas.draw_automaton(self.current_nfa.start, states)
            self.info_lbl.config(text=f"NFA Generated: {len(states)} states.")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def start_nfa_steps(self):
        regex = self.regex_entry.get().strip()
        if not regex: return
        try:
            self.step_history = self.regex_processor.get_construction_history(regex)
            self.current_step_idx = 0
            self.step_frame.pack(fill=tk.X, after=self.root.winfo_children()[1]) # Pack below controls
            self.render_step()
            self.info_lbl.config(text="Visualizing Thomson's Construction Steps...")
        except Exception as e:
            messagebox.showerror("Error", f"Step Gen Error: {e}")

    def render_step(self):
        if not self.step_history: return
        step = self.step_history[self.current_step_idx]
        
        # Update text
        desc = f"Step {self.current_step_idx}/{len(self.step_history)-1}: {step['description']}"
        if step['char']: desc += f" (Char: {step['char']})"
        self.step_lbl.config(text=desc)
        
        # Update Canvas
        nfa_list = step['stack']
        self.canvas.draw_multiple_nfas(nfa_list)

    def next_step(self):
        if self.current_step_idx < len(self.step_history) - 1:
            self.current_step_idx += 1
            self.render_step()

    def prev_step(self):
        if self.current_step_idx > 0:
            self.current_step_idx -= 1
            self.render_step()

    def close_steps(self):
        self.step_frame.pack_forget()
        self.step_history = []

    def build_dfa(self):
        self.close_steps()
        if not self.current_nfa:
            self.build_nfa()
            if not self.current_nfa: return
            
        try:
            raw_dfa = self.regex_processor.nfa_to_dfa(self.current_nfa)
            self.current_dfa = self.regex_processor.minimize_dfa(raw_dfa)
            self.canvas.draw_automaton(self.current_dfa.start, self.current_dfa.states)
            self.info_lbl.config(text=f"Minimized DFA Generated: {len(self.current_dfa.states)} states.")
            self.btn_table.config(state=tk.NORMAL)
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def show_dfa_table(self):
        if not self.current_dfa: return
        
        win = tk.Toplevel(self.root)
        win.title("DFA Transition Table")
        win.geometry("400x400")
        win.configure(bg="#1e1e2e")
        
        data = self.current_dfa.get_transition_table()
        if not data: return
        
        cols = list(data[0].keys())
        
        tree = ttk.Treeview(win, columns=cols, show="headings", style='Treeview')
        for c in cols:
            tree.heading(c, text=c)
            tree.column(c, width=80, anchor=tk.CENTER)
            
        for row in data:
            vals = [row[c] for c in cols]
            tree.insert("", tk.END, values=vals)
            
        tree.pack(fill=tk.BOTH, expand=True)

    def check_string(self):
        # ... (Identical to previous implementation) ...
        test_str = self.test_entry.get().strip()
        
        if self.current_dfa:
            self.current_dfa.reset()
            valid = True
            for char in test_str:
                if not self.current_dfa.step(char):
                    valid = False; break
            is_accepted = valid and self.current_dfa.is_accepting()
            self._show_result(is_accepted)
            
        elif self.current_nfa:
            current_states = {self.current_nfa.start}
            def epsilon_expand(states):
                stack = list(states); closure = set(states)
                while stack:
                    s = stack.pop()
                    if 'ε' in s.transitions:
                        for n in s.transitions['ε']:
                            if n not in closure:
                                closure.add(n); stack.append(n)
                return closure

            current_states = epsilon_expand(current_states)
            valid = True
            for char in test_str:
                next_states = set()
                for s in current_states:
                    if char in s.transitions:
                        next_states.update(s.transitions[char])
                if not next_states: valid = False; break
                current_states = epsilon_expand(next_states)
            
            is_accepted = valid and any(s.is_final for s in current_states)
            self._show_result(is_accepted)
        else:
            messagebox.showwarning("Warning", "Please build an automaton first.")

    def _show_result(self, accepted):
        # Create a custom popup window
        popup = tk.Toplevel(self.root)
        popup.title("Result")
        popup.geometry("300x150")
        popup.configure(bg="#1e1e2e")
        popup.resizable(False, False)
        
        # Center the popup
        popup.transient(self.root)
        popup.grab_set()
        
        frame = tk.Frame(popup, bg="#1e1e2e", padx=20, pady=20)
        frame.pack(expand=True, fill=tk.BOTH)
        
        if accepted:
            color = "#4ecdc4"
            text = "✅ Accepted!"
            emoji = "🎉"
        else:
            color = "#ff6b6b"
            text = "❌ Rejected!"
            emoji = "😞"
        
        result_label = tk.Label(frame, text=f"{emoji}\n{text}", font=("Arial", 16, "bold"), 
                               bg="#1e1e2e", fg=color, justify=tk.CENTER)
        result_label.pack(expand=True)
        
        ok_btn = tk.Button(frame, text="OK", command=popup.destroy, bg="#ff6b6b", fg="white", font=("Arial", 10, "bold"), relief=tk.FLAT, padx=10)
        ok_btn.pack(pady=10)

if __name__ == "__main__":
    root = tk.Tk()
    app = KleeneApp(root)
    root.mainloop()
