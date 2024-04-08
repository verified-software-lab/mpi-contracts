package edu.udel.cis.vsl.civl.transform.common.contracts;

import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssignsOrReadsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssumesNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.BehaviorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode.ContractKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.EnsuresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPICollectiveBlockNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.RequiresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.WaitsforNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.token.IF.Source;

/**
 * This class represents a contract block, i.e. either all of the contracts for
 * sequential properties or one MPI collective contract block. A contract block
 * contains a set of {@link ContractBehavior} which represents the body of the
 * contract block.
 * 
 * @author xxxx
 *
 */
public class FunctionContractBlock {
	/**
	 * The expression represents an MPI communicator which associates to an MPI
	 * collective block.
	 */
	private ExpressionNode mpiComm;

	/**
	 * A list of {@link ContractBehavior} which represents the body of the
	 * collective blocks.
	 */
	private List<ContractBehavior> behaviors;

	/**
	 * The big {@link Source} associates to the contract block
	 */
	private Source source;

	/**
	 * A flag indicates if the contract block is completed. A complete contract
	 * block should never contain any {@link ContractBehavior} that saves empty
	 * clauses.
	 */
	private boolean complete = false;

	private FunctionContractBlock(ExpressionNode mpiComm, Source source) {
		behaviors = new LinkedList<>();
		this.mpiComm = mpiComm;
		this.source = source;
	}

	/* *************************** static methods ***************************/
	/**
	 * Parse a chunk of contracts into several {@link FunctionContractBlock}s.
	 * Each of which represents either the whole chunk of sequential contracts
	 * or a collective block.
	 * 
	 * @param contractNodes
	 *            A sequence of {@link ContractNode}s
	 * @param nodeFactory
	 *            A reference to {@link NodeFactory}
	 * @return A list of {@link FunctionContractBlock}s which represent the
	 *         given contractNodes. If there exists any sequential contract, it
	 *         will be in the first element of the returned list.
	 */
	static List<FunctionContractBlock> parseContract(
			SequenceNode<ContractNode> contractNodes, NodeFactory nodeFactory) {
		List<FunctionContractBlock> results = new LinkedList<>();
		FunctionContractBlock seqBlock = new FunctionContractBlock(null,
				contractNodes.getSource());

		// parse default behavior:
		parseClausesInBehavior(seqBlock, contractNodes, nodeFactory);
		// parse sequential behaviors:
		for (ContractNode contract : contractNodes)
			if (contract.contractKind() == ContractKind.BEHAVIOR)
				parseClausesInBehavior(seqBlock,
						((BehaviorNode) contract).getBody(), nodeFactory);
		if (seqBlock.complete())
			results.add(seqBlock);
		// parse MPI collective blocks
		for (ContractNode contract : contractNodes)
			if (contract.contractKind() == ContractKind.MPI_COLLECTIVE) {
				FunctionContractBlock block = parseMPICollectiveBlock(
						(MPICollectiveBlockNode) contract, nodeFactory);

				if (block.complete())
					results.add(block);
			}
		return results;
	}

	/**
	 * Parse a {@link MPICollectiveBlockNode} into a
	 * {@link FunctionContractBlock}.
	 * 
	 * @param mpiBlockNode
	 *            A node represents a MPI collective contract block
	 * @param nodeFactory
	 *            A reference to {@link NodeFactory}
	 * @return An instance of {@link FunctionContractBlock}.
	 */
	static private FunctionContractBlock parseMPICollectiveBlock(
			MPICollectiveBlockNode mpiBlockNode, NodeFactory nodeFactory) {
		ExpressionNode mpiComm = mpiBlockNode.getMPIComm();
		FunctionContractBlock block = new FunctionContractBlock(mpiComm,
				mpiBlockNode.getSource());

		parseClausesInBehavior(block, mpiBlockNode.getBody(), nodeFactory);
		for (ContractNode contract : mpiBlockNode.getBody())
			if (contract.contractKind() == ContractKind.BEHAVIOR)
				parseClausesInBehavior(block,
						((BehaviorNode) contract).getBody(), nodeFactory);
		return block;
	}

	/**
	 * Parse a behavior block into an instance of {@link ContractBehavior} and
	 * adds it to associated {@link FunctionContractBlock}.
	 * 
	 * @param currentBlock
	 *            The contract block where the behavior block is in.
	 * @param contracts
	 *            A sequence of contracts representing a behavior block
	 * @param nodeFactory
	 *            A reference to {@link NodeFactory}
	 */
	static private void parseClausesInBehavior(
			FunctionContractBlock currentBlock,
			SequenceNode<ContractNode> contracts, NodeFactory nodeFactory) {
		List<ExpressionNode> assumptions = new LinkedList<>();
		ContractBehavior condClauses;

		// Collects assumptions:
		for (ContractNode contract : contracts)
			if (contract.contractKind() == ContractKind.ASSUMES) {
				ExpressionNode condition = ((AssumesNode) contract)
						.getPredicate();

				assumptions.add(condition);
			}
		condClauses = currentBlock.new ContractBehavior(assumptions);
		// Collects clauses which specifies predicates:
		for (ContractNode contract : contracts) {
			ContractKind kind = contract.contractKind();

			switch (kind) {
				case REQUIRES :
					condClauses.addRequires(((RequiresNode) contract));
					break;
				case ENSURES :
					condClauses.addEnsures(((EnsuresNode) contract));
					break;
				case WAITSFOR :
					condClauses.addWaitsfor(
							((WaitsforNode) contract).getArguments());
					break;
				case ASSIGNS_READS : {
					AssignsOrReadsNode assigns = (AssignsOrReadsNode) contract;
					SequenceNode<ExpressionNode> memList;

					if (!assigns.isAssigns())
						break;
					memList = assigns.getMemoryList();
					if (memList.numChildren() <= 0
							|| memList.getSequenceChild(0)
									.expressionKind() != ExpressionKind.NOTHING)
						condClauses.addAssigns(assigns.getMemoryList());
					break;
				}
				default :
					// do nothing.
			}
		}
		currentBlock.addConditionalClauses(condClauses);
	}

	/* *********************** package private getters ***********************/
	public boolean isSequentialBlock() {
		return mpiComm == null;
	}

	public ExpressionNode getMPIComm() {
		return mpiComm;
	}

	public Source getContractBlockSource() {
		return source;
	}

	public Iterable<ContractBehavior> getBehaviorsInBlock() {
		return behaviors;
	}

	/**
	 * Clean up all {@link ContractBehavior} in this contract block. If a
	 * {@link ContractBehavior} has empty clauses, remove it.
	 * 
	 * @return True if and only if there is at least one
	 *         {@link ContractBehavior} remaining at the end of the function.
	 */
	boolean complete() {
		List<ContractBehavior> newBehaviors = new LinkedList<>();

		for (ContractBehavior behav : behaviors) {
			if (!(behav.getRequires().isEmpty() && behav.getEnsures().isEmpty()
					&& behav.waitsforSet.isEmpty()
					&& behav.getAssignsArgs().isEmpty()))
				newBehaviors.add(behav);
		}
		complete = true;
		behaviors = newBehaviors;
		return !behaviors.isEmpty();
	}

	/**
	 * <p>
	 * <b>Pre-condition:</b> The contract block must be complete
	 * </p>
	 * 
	 * @return A list of {@link ContractBehavior} which is the body of the
	 *         contract block.
	 */
	List<ContractBehavior> getConditionalClauses() {
		assert complete : "Cannot get ConditionalClauses before the contract block is complete";
		return behaviors;
	}

	/**
	 * <p>
	 * <b>Pre-condition:</b> The contract block must NOT be complete
	 * </p>
	 * <p>
	 * <b>Summary:</b> Add a {@link ContractBehavior} into the contract block.
	 * </p>
	 */
	void addConditionalClauses(ContractBehavior clauses) {
		assert !complete : "Cannot add ConditionalClauses after the contract block is complete";
		behaviors.add(clauses);
	}

	/**
	 * This class represents a contract behavior. Without loss of generality,
	 * there is always a default behavior which has no assumption and no name.
	 */
	public class ContractBehavior {
		/**
		 * The condition which comes from the assumption of a behavior:
		 */
		private List<ExpressionNode> conditions;

		private List<ExpressionNode> requires;

		private List<ExpressionNode> ensures;

		private List<ExpressionNode> waitsforSet;

		private List<ExpressionNode> assignsSet;

		private ContractBehavior(List<ExpressionNode> conditions) {
			this.conditions = conditions;
			requires = new LinkedList<>();
			ensures = new LinkedList<>();
			waitsforSet = new LinkedList<>();
			assignsSet = new LinkedList<>();
		}

		/**
		 * Add an expression of a "requires" clause.
		 * 
		 * @param requires
		 */
		void addRequires(RequiresNode requires) {
			this.requires.add(requires.getExpression());
		}

		/**
		 * Add an expression of a "ensures" clause.
		 * 
		 * @param requires
		 */
		void addEnsures(EnsuresNode ensures) {
			this.ensures.add(ensures.getExpression());
		}

		/**
		 * Add a set of arguments of a "waitsfor" clause.
		 * 
		 * @param requires
		 */
		void addWaitsfor(SequenceNode<ExpressionNode> waitsforArgs) {
			for (ExpressionNode arg : waitsforArgs) {
				waitsforSet.add(arg);
			}
		}

		/**
		 * Add a set of arguments of a "assigns" clause.
		 * 
		 * @param assignsArgs
		 */
		void addAssigns(SequenceNode<ExpressionNode> assignsArgs) {
			for (ExpressionNode arg : assignsArgs)
				assignsSet.add(arg);
		}

		/**
		 * Returns all requires expressions in this contract behavior
		 * 
		 * @return
		 */
		public List<ExpressionNode> getRequires() {
			return requires;
		}

		/**
		 * Returns all ensures expressions in this contract behavior
		 * 
		 * @return
		 */
		public List<ExpressionNode> getEnsures() {
			return ensures;
		}

		/**
		 * @param nodeFactory
		 * @return a list of tuples (term, restrict, binders)
		 */
		public List<ExpressionNode> getWaitsfors() {
			return waitsforSet;
		}

		/**
		 * 
		 * @return a list of tuples (term, restrict, binders)
		 * 
		 */
		public List<ExpressionNode> getAssignsArgs() {
			return assignsSet;
		}

		/**
		 * Return a list of "condition" expressions which are specified by ACSL
		 * "assumes" keywords
		 */
		public List<ExpressionNode> getConditions() {
			return conditions;
		}
	}
}
