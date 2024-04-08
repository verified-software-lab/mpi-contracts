package edu.udel.cis.vsl.civl.library.mpi;

import java.util.Iterator;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract.ContractKind;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPrimitiveType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * <p>
 * This class represents a library executor for MPI libraries. This class is
 * responsible for processing following executions:
 * <ul>
 * <li><b>System functions defined in MPI libraries:</b>
 * <ul>
 * <li>$mpi_set_status</li>
 * <li>$mpi_get_status</li>
 * <li>$mpi_assert_consistent_base_type</li>
 * <li>$mpi_newGcomm</li>
 * <li>$mpi_getGcomm</li>
 * <li>$mpi_root_scope</li>
 * <li>$mpi_proc_scope</li>
 * </ul>
 * </li>
 * <li><b>Collective evaluation algorithm:</b>
 * {@link #executeCoassertWorker(State, int, String, Expression[], SymbolicExpression[], CIVLSource, boolean, ContractKind, Variable[])}
 * </li>
 * </ul>
 * </p>
 * 
 * @author xxxx
 * 
 */
public class LibmpiExecutor extends BaseLibraryExecutor
		implements
			LibraryExecutor {
	private LibmpiEvaluator libEvaluator;

	public LibmpiExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
		this.libEvaluator = new LibmpiEvaluator(name, evaluator, modelFactory,
				symbolicUtil, symbolicAnalyzer, civlConfig, libEvaluatorLoader);
	}
	/* ************************* private methods **************************** */

	@Override
	protected Evaluation executeValue(State state, int pid, String process,
			CIVLSource source, String functionName, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Evaluation callEval = null;

		switch (functionName) {
			case "$mpi_set_status" :
				callEval = executeSetStatus(state, pid, arguments,
						argumentValues);
				break;
			case "$mpi_get_status" :
				callEval = executeGetStatus(state, pid);
				break;
			case "$mpi_check_buffer" :
				callEval = executeMpiCheckBuffer(state, pid, process, arguments,
						argumentValues, source);
				break;
			case "$mpi_new_gcomm" :
				callEval = executeNewGcomm(state, pid, process, arguments,
						argumentValues, source);
				break;
			case "$mpi_get_gcomm" :
				callEval = executeGetGcomm(state, pid, process, arguments,
						argumentValues, source);
				break;
			case "$mpi_root_scope" :
				callEval = executeRootScope(state, pid, process, arguments,
						argumentValues, source);
				break;
			case "$mpi_proc_scope" :
				callEval = executeProcScope(state, pid, process, arguments,
						argumentValues, source);
				break;
			case "$mpi_pointer_add_sys" :
				callEval = executePointerAdd(state, pid, process, arguments,
						argumentValues, source);
				break;
			default :
				throw new CIVLInternalException(
						"Unknown civl-mpi function: " + name, source);
		}
		return callEval;
	}

	/**
	 * Executes system function
	 * <code>CMPI_Set_status($mpi_sys_status newStatus)</code>. Set the variable
	 * "_my_status" added by
	 * {@link edu.udel.cis.vsl.civl.transform.IF.MPI2CIVLTransformer} the given
	 * new value
	 * 
	 * @param state
	 *            the current state
	 * @param pid
	 *            the PID of the process
	 * @param call
	 *            the statement expression of the function call
	 * @param arguments
	 *            an array of expressions of arguments of the function
	 * @param argumentValues
	 *            an array of symbolic expressions of arguments of the function
	 * @return
	 */
	private Evaluation executeSetStatus(State state, int pid,
			Expression[] arguments, SymbolicExpression[] argumentValues) {
		SymbolicExpression newStatus = argumentValues[0];
		Pair<Integer, Variable> myStatusVarInfo;
		State newState;

		myStatusVarInfo = getVariableWTDynamicScoping(state, pid,
				"_mpi_process", "_mpi_status");
		newState = this.stateFactory.setVariable(state,
				myStatusVarInfo.right.vid(), myStatusVarInfo.left, newStatus);
		return new Evaluation(newState, null);
	}

	private Evaluation executeGetStatus(State state, int pid)
			throws UnsatisfiablePathConditionException {
		// variable (right in pair) and it's static scope
		Pair<Integer, Variable> myStatusVarInfo;
		SymbolicExpression valueOfMyStatusVar;
		// String process = state.getProcessState(pid).name() + "(id=" + pid +
		// ")";

		myStatusVarInfo = getVariableWTDynamicScoping(state, pid,
				"_mpi_process", "_mpi_status");
		valueOfMyStatusVar = state.getDyscope(myStatusVarInfo.left)
				.getValue(myStatusVarInfo.right.vid());
		return new Evaluation(state, valueOfMyStatusVar);
	}

	/**
	 * Search a variable with a scoping rule similar to dynamic scoping. Given a
	 * variable name and a function name, this method will search for each call
	 * stack entry e and all ancestors of e from the top stack entry e0, it
	 * looks for the first matched variable appears in the matched function
	 * scope.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param functionName
	 *            The name of the function
	 * @param varName
	 *            The name of the variable
	 * @return
	 */
	private Pair<Integer, Variable> getVariableWTDynamicScoping(State state,
			int pid, String functionName, String varName) {
		Iterator<? extends StackEntry> stackIter = state.getProcessState(pid)
				.getStackEntries().iterator();
		DynamicScope currDyscope = null;
		int currDyscopeId = -1;

		while (stackIter.hasNext()) {
			currDyscopeId = stackIter.next().scope();

			while (currDyscopeId > 0) {
				currDyscope = state.getDyscope(currDyscopeId);
				if (currDyscope.lexicalScope().containsVariable(varName))
					if (currDyscope.lexicalScope().function().name().name()
							.equals(functionName))
						return new Pair<>(currDyscopeId,
								currDyscope.lexicalScope().variable(varName));
				currDyscopeId = currDyscope.getParent();
			}
		}
		return new Pair<>(currDyscopeId, null);
	}

	/**
	 * <p>
	 * <b>Summary: </b> Executing the function
	 * <code>$mpi_assert_consistent_base_type(void * ptr, MPI_Datatype datatype)</code>
	 * 
	 * This system function checks if the base type of an MPI_Datatype is
	 * consistent with the base type of the object pointed by the given pointer.
	 * 
	 * </p>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The String identifier of the process
	 * @param arguments
	 *            {@link Expression}s of arguments of the system function
	 * @param argumentValues
	 *            {@link SymbolicExpression}s of arguments of the system
	 *            function
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeMpiCheckBuffer(State state, int pid,
			String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		CIVLSource ptrSource = arguments[0].getSource();
		SymbolicExpression pointer = argumentValues[0];
		NumericExpression assertedType = (NumericExpression) argumentValues[2],
				primitiveTypeCount, count;
		CIVLType realType;
		SymbolicType realSymType, assertedSymType;
		Reasoner reasoner;
		IntegerNumber assertedTypeEnum;
		Pair<BooleanExpression, ResultType> checkPointer;
		Pair<CIVLPrimitiveType, NumericExpression> mpiType2Civl = null;
		Evaluation eval;

		count = (NumericExpression) argumentValues[1];
		reasoner = universe.reasoner(state.getPathCondition(universe));
		if (reasoner.isValid(universe.equals(count, zero))
				|| pointer.isNull()) {
			return new Evaluation(state, null);
		}
		if (symbolicUtil.isNullPointer(pointer))
			return new Evaluation(state, null);
		// this assertion doesn't need recovery:
		if (!pointer.operator().equals(SymbolicOperator.TUPLE)) {
			errorLogger.logSimpleError(arguments[0].getSource(), state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.POINTER,
					"attempt to read/write a non-concrete pointer type variable");
			return new Evaluation(state, null);
		}
		checkPointer = symbolicAnalyzer.isDerefablePointer(state, pointer);
		if (checkPointer.right != ResultType.YES) {
			state = errorLogger.logError(arguments[0].getSource(), state, pid,
					this.symbolicAnalyzer.stateInformation(state),
					checkPointer.left, checkPointer.right, ErrorKind.POINTER,
					"attempt to read/write a invalid pointer type variable");
			// return state;
		}
		realType = symbolicAnalyzer.getArrayBaseType(state, ptrSource, pointer);
		realSymType = realType.getDynamicType(universe);
		assertedTypeEnum = (IntegerNumber) reasoner.extractNumber(assertedType);
		if (assertedTypeEnum != null)
			mpiType2Civl = LibmpiEvaluator.mpiTypeToCIVLType(universe,
					typeFactory, assertedTypeEnum.intValue(), source);
		else
			throw new CIVLInternalException(
					"Executing $mpi_check_buffer(void *, int, MPI_Datatype) with arbitrary MPI_Datatype.",
					source);
		assertedSymType = mpiType2Civl.left.getDynamicType(universe);
		primitiveTypeCount = mpiType2Civl.right;
		// assertion doesn't need recovery:
		if (!assertedSymType.equals(realSymType)) {
			errorLogger.logSimpleError(source, state, process,
					this.symbolicAnalyzer.stateInformation(state),
					ErrorKind.MPI_ERROR,
					"The primitive type " + realType.toString()
							+ " of the object pointed by the input pointer argument ["
							+ ptrSource.getLocation() + ":" + arguments[0]
							+ "] of"
							+ " MPI routines is not consistent with the specified MPI_Datatype.");
		}
		eval = evaluator.dereference(source, state, process, pointer, false,
				true);
		state = eval.state;
		count = universe.multiply(primitiveTypeCount, count);
		// TODO: here needs be improved:
		if (reasoner.isValid(universe.equals(count, one)))
			return new Evaluation(state, null);
		try {
			libEvaluator.getDataFrom(state, pid, process, arguments[0], pointer,
					count, true, false, ptrSource);
		} catch (UnsatisfiablePathConditionException e) {
			errorLogger.logSimpleError(source, state, process,
					symbolicAnalyzer.stateInformation(state),
					ErrorKind.MPI_ERROR,
					"The type of the object pointed by " + arguments[0]
							+ " is inconsistent with the specified MPI datatype signiture.");
		}
		return new Evaluation(state, null);
	}

	/**
	 * add new CMPI_Gcomm to seq
	 * 
	 * @param state
	 * @param pid
	 * @param process
	 * @param arguments
	 * @param argumentValues
	 * @param source
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Evaluation executeNewGcomm(State state, int pid, String process,
			Expression arguments[], SymbolicExpression argumentValues[],
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression mpiRootScope = argumentValues[0];
		SymbolicExpression newCMPIGcomm = argumentValues[1];
		int sid = stateFactory.getDyscopeId(mpiRootScope);
		Variable gcommsVar = state.getDyscope(sid).lexicalScope()
				.variable("_mpi_gcomms");
		SymbolicExpression gcomms;
		NumericExpression idx;

		gcomms = state.getVariableValue(sid, gcommsVar.vid());
		idx = universe.length(gcomms);
		gcomms = universe.append(gcomms, newCMPIGcomm);
		state = stateFactory.setVariable(state, gcommsVar.vid(), sid, gcomms);
		return new Evaluation(state, idx);
	}

	private Evaluation executeGetGcomm(State state, int pid, String process,
			Expression arguments[], SymbolicExpression argumentValues[],
			CIVLSource source) throws UnsatisfiablePathConditionException {
		NumericExpression index = (NumericExpression) argumentValues[1];
		SymbolicExpression scope = argumentValues[0];
		SymbolicExpression gcomms, gcomm;
		int sid = stateFactory.getDyscopeId(scope);
		Variable gcommsVar = state.getDyscope(sid).lexicalScope()
				.variable("_mpi_gcomms");

		gcomms = state.getVariableValue(sid, gcommsVar.vid());
		gcomm = universe.arrayRead(gcomms, index);
		return new Evaluation(state, gcomm);
	}

	private Evaluation executeRootScope(State state, int pid, String process,
			Expression arguments[], SymbolicExpression argumentValues[],
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression gcommHandle;
		SymbolicExpression scopeVal;
		Evaluation eval;
		int sid;

		eval = evaluator.dereference(source, state, process, commHandle, false,
				true);
		state = eval.state;
		gcommHandle = universe.tupleRead(eval.value, oneObject);
		sid = stateFactory
				.getDyscopeId(symbolicUtil.getScopeValue(gcommHandle));
		scopeVal = stateFactory.scopeValue(sid);
		return new Evaluation(state, scopeVal);
	}

	private Evaluation executeProcScope(State state, int pid, String process,
			Expression arguments[], SymbolicExpression argumentValues[],
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression commHandle = argumentValues[0];
		SymbolicExpression scopeVal;
		int sid;

		sid = stateFactory.getDyscopeId(symbolicUtil.getScopeValue(commHandle));
		scopeVal = stateFactory.scopeValue(sid);
		return new Evaluation(state, scopeVal);
	}

	// almost identical to the old \mpi_offset
	private Evaluation executePointerAdd(State state, int pid, String process,
			Expression arguments[], SymbolicExpression argumentValues[],
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression ptrVal = argumentValues[0];
		NumericExpression countVal = (NumericExpression) argumentValues[1];
		NumericExpression typesizeVal = (NumericExpression) argumentValues[2];
		Pair<SymbolicExpression, NumericExpression> ptr_primTypeCount = LibmpiEvaluator
				.processMPIPointer(state, pid, process, ptrVal, typesizeVal,
						source, symbolicAnalyzer, symbolicUtil, evaluator);

		return evaluator.arrayElementReferenceAdd(state, pid,
				ptr_primTypeCount.left,
				universe.multiply(countVal, ptr_primTypeCount.right),
				source).left;
	}
}
