package edu.udel.cis.vsl.gmc;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;

import edu.udel.cis.vsl.gmc.seq.DfsSearcher;
import edu.udel.cis.vsl.gmc.seq.StateManager;

/**
 * A {@link Simulator} is used to execute a transition system using a
 * {@link TransitionChooser} to determine which transition to execute from each
 * state. E.g., this could be used to replay an execution trace of a transition
 * system, for which the trace was stored in a file created by method
 * {@link DfsSearcher#writeStack(File)}. Or, it could be used to perform a
 * random execution.
 * 
 * @author xxxx
 * 
 * @param <STATE>
 *            the type for the states in the transition system
 * @param <TRANSITION>
 *            the type for the transitions in the transition system
 */
public class Simulator<STATE, TRANSITION> {

	// Instance fields...

	/**
	 * The state manager: the object used to determine the next state given a
	 * state and a transition.
	 */
	private StateManager<STATE, TRANSITION> manager;

	/**
	 * The stream to which the human-readable output should be sent when
	 * replaying a trace.
	 */
	private PrintStream out;

	private PrintStream dump = new PrintStream(new OutputStream() {
		@Override
		public void write(int b) throws IOException {
			// doing nothing
		}
	});

	/**
	 * Print the states at each step in the trace? If this is false, only the
	 * initial and the final states will be printed.
	 */
	private boolean printAllStates = true;

	/**
	 * If "-quiet" is used in the command?
	 */
	private boolean quiet = false;

	private StatePredicateIF<STATE> predicate = null;

	private ErrorLog log = null;

	// Constructors...

	/**
	 * 
	 * @param enabler
	 *                    enabler used to determine the set of enabled
	 *                    transitions at a given state
	 * @param manager
	 *                    state manager; used to compute the next state given a
	 *                    state and transition
	 * @param out
	 *                    stream to which the trace should be written in
	 *                    human-readable form
	 */
	public Simulator(StateManager<STATE, TRANSITION> manager, PrintStream out) {
		this.manager = manager;
		this.out = out;
	}

	// Instance methods: helpers...

	/**
	 * Prints out those states which should be printed. A utility method used by
	 * play method.
	 * 
	 * @param step
	 *                           the step number to use in the printout
	 * @param numStates
	 *                           the number of states in the array states
	 * @param executionNames
	 *                           the names to use for each state; array of
	 *                           length numStates
	 * @param print
	 *                           which states should be printed; array of
	 *                           boolean of length numStates
	 * @param states
	 *                           the states; array of STATE of length numStates
	 */
	private void printStates(int step, int numStates, String[] executionNames,
			boolean[] print, STATE[] states) {
		for (int i = 0; i < numStates; i++) {
			if (print[i]) {
				if (quiet) {
					dump.println();
					manager.printStateLong(dump, states[i]);
					dump.println();
				} else {
					out.println();
					manager.printStateLong(out, states[i]);
					out.println();
				}
			}
		}
	}

	// Instance methods: public...

	public void setPredicate(StatePredicateIF<STATE> predicate) {
		this.predicate = predicate;
	}

	public StatePredicateIF<STATE> getPredicate() {
		return predicate;
	}

	public void setPrintAllStates(boolean value) {
		this.printAllStates = value;
	}

	public boolean getPrintAllStates() {
		return printAllStates;
	}

	public void setLog(ErrorLog log) {
		this.log = log;
	}

	public ErrorLog getLog() {
		return log;
	}

	public boolean isQuiet() {
		return quiet;
	}

	public void setQuiet(boolean quiet) {
		this.quiet = quiet;
	}

	public Trace<TRANSITION, STATE>[] play(STATE initialState,
			TransitionChooser<STATE, TRANSITION> chooser, boolean verbose)
			throws MisguidedExecutionException {
		@SuppressWarnings("unchecked")
		STATE[] stateArray = (STATE[]) new Object[]{initialState};
		boolean[] printArray = new boolean[]{true};
		String[] names = new String[]{null};

		return play(stateArray, printArray, names, chooser, verbose);
	}

	/**
	 * Plays the trace. This method accepts an array of initial states, and will
	 * create executions in parallel, one for each initial state. All of the
	 * executions will use the same sequence of transitions, but may start from
	 * different initial states. The common use case has two initial states, the
	 * first one a symbolic state and the second a concrete state obtained by
	 * solving the path condition.
	 * 
	 * @param states
	 *                    the states from which the execution should start. The
	 *                    first state in the initial state (index 0) will be the
	 *                    one assumed to execute according to the guide. This
	 *                    method will modify this array so that upon returning
	 *                    the array will hold the final states.
	 * @param print
	 *                    which states should be printed at a point when states
	 *                    will be printed. Array of length states.length.
	 * @param names
	 *                    the names to use for the different executions. Array
	 *                    of length states.length
	 * @param chooser
	 *                    the object used to decide which transition to choose
	 *                    when more than one is enabled at a state
	 * @param verbose
	 *                    print verbose output about what's going on?
	 * @return An array of traces after executing the trace with different
	 *         initial states. See also {@link Trace}.
	 * @throws MisguidedExecutionException
	 */
	@SuppressWarnings("unchecked")
	public Trace<TRANSITION, STATE>[] play(STATE states[], boolean print[],
			String[] names, TransitionChooser<STATE, TRANSITION> chooser,
			boolean verbose) throws MisguidedExecutionException {
		int step = 0;
		int numExecutions = states.length;
		String[] executionNames = new String[1];
		TRANSITION transition;
		TraceStepIF<STATE> traceStep;
		Trace<TRANSITION, STATE>[] traces = new Trace[numExecutions];

		for (int i = 0; i < numExecutions; i++) {
			String name = names[i];

			if (name == null)
				executionNames[i] = "";
			else
				executionNames[i] = " (" + names + ")";
			traces[i] = new Trace<TRANSITION, STATE>(executionNames[i],
					states[i]);
		}
		if (verbose) {
			out.println("\nInitial state:");
			printStates(step, 1, executionNames, print, states);
		}
		while (true) {
			boolean hasNewTransition = false;
			STATE[] newStates = (STATE[]) new Object[numExecutions];

			if (predicate != null) {
				for (int i = 0; i < numExecutions; i++) {
					STATE state = traces[i].lastState();
					if (predicate.holdsAt(state)) {
						if (!quiet) {
							if (!printAllStates) {
								out.println();
								manager.printStateLong(out, state);
							}
							out.println();
							out.println("Violation of " + predicate
									+ " found in " + state + ":");
							out.println(predicate.explanation());
							out.println();
						}
						traces[i].setViolation(true);
					}
				}
			}
			for (int i = 0; i < numExecutions; i++) {
				STATE current = traces[i].lastState();

				transition = chooser.chooseEnabledTransition(current);
				if (transition == null) {
					newStates[i] = null;
					continue;
				}
				hasNewTransition = true;
				traceStep = manager.nextState(current, transition);
				manager.normalize(traceStep);
				traces[i].addTraceStep(traceStep);
				manager.printTraceStep(current, traceStep);
				newStates[i] = traceStep.getFinalState();
				manager.printTraceStepFinalState(newStates[i], -1);
			}
			if (!hasNewTransition)
				break;
			step++;
			if (verbose)
				out.print("\nStep " + step + ": ");
			if (printAllStates)
				printStates(step, 1, executionNames, print, newStates);
		}
		if (!quiet) {
			out.println("Trace ends after " + step + " trace steps.");
		}
		return traces;
	}

	public Trace<TRANSITION, STATE>[] play(STATE initialSymbolicState,
			STATE initialConcreteState, boolean printSymbolicStates,
			TransitionChooser<STATE, TRANSITION> chooser, boolean verbose)
			throws MisguidedExecutionException {
		@SuppressWarnings("unchecked")
		STATE[] stateArray = (STATE[]) new Object[]{initialSymbolicState,
				initialConcreteState};
		boolean[] printArray = new boolean[]{printSymbolicStates, true};
		String[] names = new String[]{"Symbolic", "Concrete"};

		return play(stateArray, printArray, names, chooser, verbose);
	}

}
