package othello.ai;

import othello.game.*;
import othello.game.OthelloGame;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class McNode implements Node {

    private State state;
    private Node parent;

    private List<Node> childArray;

    private Node currentNode;

    //private double uctValue;

    private int numSims;

    private Score score;

    public McNode(Node parent, State state) {
        this.parent = parent;
        this.state = state;
        numSims = 0;
        childArray = new ArrayList<>();
        score = new Score(((OthelloGame) state.getGame()).getPlayer1(), ((OthelloGame) state.getGame()).getPlayer2(), 0, 0);
    }

    public Node getParent() {
        return parent;
    }

    public State getState() {
        return state;
    }

    public List<Node> getChildArray() {
        return childArray;
    }

    public Score getScore() {
        return score;
    }

    public int getNumSims() {
        return numSims;
    }

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

    private double getUctValue(Node child) { //New UCT class?
        double uctValue;
        if (((McNode) child).getNumSims() == 0) {
            uctValue = 1;
        } else {
            uctValue = (child.getRewardForPlayer(child.getState().getPlayer())) / (((McNode) child).getNumSims() * 1.0)
                    + (Math.sqrt(0.7 * (Math.log(getNumSims() * 1.0) / ((McNode) child).getNumSims())));
        }
        return uctValue;
    }

    public Node expandNode(OthelloGame game) {
        if (!canExpandNode()) {
            return this;
        }
        Random random = new Random();
//        Random random = new Random();
//        int randomMoveIndex = random.nextInt(this.getState().getUnexploredMoves().size());
//
//        Move randomMove = state.getUnexploredMoves().remove(randomMoveIndex);
//        Move newMove = new TicTacToeMove(game.getMark(), ((TicTacToeMove) randomMove).getRow(), ((TicTacToeMove) randomMove).getColumn());
//        game.doMove(newMove);

        List<Move> moves = state.getUnexploredMoves(); //Gets all the moves from that state.
        List<int[]> validIndices = this.getState().getValidIndices(); //Gets the valid indices for that player for the current state. Not biases, all duplicates have been removed.

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
        if (!randomMoves.isEmpty()) { //why would random moves be empty: on a pass turn?
            game.doMove(randomMoves);
        }
        game.nextTurn(); //go to next turn to create new nodes.

        if (game.getValidMoves(game.getTurn().getMark()).isEmpty()) {
            game.nextTurn();
        }
        McNode child = new McNode(this, new State(game, randomMoves)); //goes to next turn and checks for valid moves

        //TODO: if this leads to a turn with no valid moves, do another next turn and create that node.

        childArray.add(child); //requires child to not be null.
        return child;
    }

    public boolean canExpandNode() {
        return state.getUnexploredMoves().size() > 0;
    }

    public void backPropagation(Score score) { //TODO: give backpropagation the average of the scores.
        this.getScore().incScore(score);
        this.numSims++;
        if (getParent() != null) {
            ((McNode) getParent()).backPropagation(score);
        }
    }

    public double getRewardForPlayer(Player player) {
        return score.getScorePlayer(player);
    }

    public Node getNodeWithMostVisits() {
        int mostVisits = 0;
        Node bestChild = null;

        for (Node child : childArray) {
            if (((McNode) child).getNumSims() > mostVisits) {
                bestChild = child;
                mostVisits = ((McNode) child).getNumSims();
            }
        }

        return bestChild;
    }

//    public Move moveToThisParentNode() {
//        return state.getMoveToParent();
//    }

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