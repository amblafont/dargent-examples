To debug, put a breakpoint on the first Left constructor in trace_solve_tac
Then, you can evaluate get_tacs data0 in the debugger and try to find its origin.
For instance, the constructor BlackBoxTac is used in CogentHelper
