package othello.ai;

import othello.game.*;
import othello.game.OthelloGame;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * Node for the MCTS method that is responsible for managing other nodes through selection, expansion and backpropagation.
 */
public class McNode implements Node {

    private State state;
    private Node parent;

    private List<Node> childArray;

    private Node currentNode;

    /**
     * Number of simulations indicates how often a node has been visited.
     */
    private int numSims;

    private Score score;

    public McNode(Node parent, State state) {
        this.parent = parent;
        this.state = state;
        numSims = 0;
        childArray = new ArrayList<>();
        score = new Score(((OthelloGame) state.getGame()).getPlayer1(), ((OthelloGame) state.getGame()).getPlayer2(), 0, 0);
    }

    /**
     * Gets the parent node of a node.
     *
     * @return the parent node.
     */
    public Node getParent() {
        return parent;
    }

    /**
     * Gets the state of a node.
     *
     * @return the state of the node.
     */
    public State getState() {
        return state;
    }

    /**
     * Gets the child array of a node.
     *
     * @return a list of child nodes.
     */
    public List<Node> getChildArray() {
        return childArray;
    }

    /**
     * Gets the score of a node.
     *
     * @return the score of a node.
     */
    public Score getScore() {
        return score;
    }

    /**
     * Gets the number of simulation a node has gone through, in other words how often it has been visited.
     *
     * @return an integer representing the number of simulations.
     */
    public int getNumSims() {
        return numSims;
    }

    /**
     * Selects a node from a node's children based on their uct value.
     *
     * @return the node with the highest uct value.
     */
    public Node selectNode() { //UCB1 is a selection policy
        currentNode = this;
        double max = Integer.MIN_VALUE;
        for (Node child : childArray) {
            double uctValue = getUctValue(child);
            if (uctValue > max) {
                max = uctValue;
                currentNode = child; //Why the current node?
            }
        }
        return currentNode;
    }

    /**
     * Calculates the uct value of a node with the UCB1 algorithm.
     *
     * @param child node for which the uct value should be calculated
     * @return the uct value of the node.
     */
    private double getUctValue(Node child) { //New UCT class?
        double uctValue;
        if (((McNode) child).getNumSims() == 0) {
            uctValue = 1;
        } else {
            uctValue = (child.getScoreForPlayer(child.getState().getPlayer())) / (((McNode) child).getNumSims() * 1.0)
                    + (Math.sqrt(0.7 * (Math.log(getNumSims() * 1.0) / ((McNode) child).getNumSims())));
        }
        return uctValue;
    }

    /**
     * Expands a node by taking the current state of the game. The valid moves from that state are taken, from which
     * one move is randomly selected and performed on the game. The resulting game state and the performed move are
     * used to create another node.
     *
     * @param game that is used to expand the node.
     * @return a new child node for the new state of the game.
     */
    public Node expandNode(OthelloGame game) {
        if (!canExpandNode()) {
            return this;
        }
        Random random = new Random();

        List<Move> moves = state.getUnexploredMoves(); //Gets all the moves from that state.
        List<int[]> validIndices = this.getState().getValidIndices(); //Gets the valid indices for that player for the current state. No biases, all duplicates have been removed.

        int index = random.nextInt(validIndices.size()); //Get a random row/column pair from the valid indices.
        int[] movePair = validIndices.remove(index);
        int row = movePair[0];
        int col = movePair[1];

        List<Move> randomMoves = new ArrayList<>(); //The random moves  for all directions
        for (Move m : moves) {
            if (m.getRow() == row && m.getCol() == col) {
                randomMoves.add(m);
                //this move is going to be explored and should be removed.
            }
        }
        for (Move m : randomMoves) {
            state.getUnexploredMoves().remove(m); //Remove all those moves from that state's unexplored moves.
        }
//        if (!randomMoves.isEmpty()) { //Only actual valid moves available should they be played.
//            game.doMove(randomMoves);
//        }
        game.nextTurn(); //go to next turn to create new nodes.

        if (game.getValidMoves(game.getTurn().getMark()).isEmpty()) { //If the next turn results in no valid moves, skip that turn.
            game.nextTurn();
        }

        McNode child = new McNode(this, new State(game, randomMoves));

        childArray.add(child);
        return child;
    }

    /**
     * Checks if a node can be expanded based on how many unexplored there are left from that state.
     *
     * @return whether the node can be expanded.
     */
    public boolean canExpandNode() {
        return state.getUnexploredMoves().size() > 0;
    }

    /**
     * Back-propagates a score to the parents of nodes.
     *
     * @param score the score that should be back-propagated.
     */
    public void backPropagation(Score score) { //TODO: give backpropagation the average of the scores.
        this.getScore().incScore(score);
        this.numSims++;
        if (getParent() != null) {
            ((McNode) getParent()).backPropagation(score);
        }
    }

    /**
     * Gets the score for a player, which is the result of the rollout of the current node's state.
     *
     * @param player for whom the score should be retrieved.
     * @return the score of the selected player.
     */
    public double getScoreForPlayer(Player player) {
        return score.getScorePlayer(player);
    }

    /**
     * Finds which child node has been simulated the most,can also be considered as to how often a node has been visited.
     *
     * @return the child node with the most simulations.
     */
    public Node getNodeWithMostSims() {
        int mostSims = 0;
        Node bestChild = null;

        for (Node child : childArray) {
            if (((McNode) child).getNumSims() > mostSims) {
                bestChild = child;
                mostSims = ((McNode) child).getNumSims();
            }
        }

        return bestChild;
    }

    /**
     * Prints the search tree of a node.
     */
    public void printTree() {
        String playerRewards = "";

        for (var key : score.getScores().keySet()) {
            playerRewards += String.format("%s: %s", key, score.getScorePlayer((Player) key));
        }
        System.out.println(String.format("Player: %s, Move: %s, Simulations: %s, Rewards: %s", this.state.getPlayer(), state.moveToParent != null ? state.moveToParent : null, numSims, playerRewards));
        for (Node child : childArray) {
            ((McNode) child).printTree();
        }
    }
}