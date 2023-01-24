package othello.ai;

import othello.game.Move;
import othello.game.OthelloGame;
import othello.game.Player;
import othello.game.OthelloGame;
import othello.game.OthelloMove;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class McNode implements Node {

    private State state;
    private Node parent;

    private int visitCount;

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

    public void incrementVisit() {
        visitCount += 1;
    }

    public int getVisitCount() {
        return visitCount;
    }

    public Score getScore() {
        return score;
    }

    public int getNumSims() {
        return numSims;
    }

    public Node selectNode() {
        currentNode = this;
        double max = Integer.MIN_VALUE;
        for (Node child : childArray) {
            double uctValue = getUctValue(child);
            if (uctValue > max) {
                max = uctValue;
                currentNode = child;
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
                    + (Math.sqrt(2 * (Math.log(getNumSims() * 1.0) / ((McNode) child).getNumSims())));
        }
        Random r = new Random();
        uctValue += (r.nextDouble() / 10000000); //randomness c?
        return uctValue;
    }

    public Node expandNode(OthelloGame game) {
        if (!canExpandNode()) {
            return this;
        }
        Random random = new Random();
        int randomMoveIndex = random.nextInt(this.getState().getUnexploredMoves().size());

        Move randomMove = state.getUnexploredMoves().remove(randomMoveIndex);
        Move newMove = new TicTacToeMove(game.getMark(), ((TicTacToeMove) randomMove).getRow(), ((TicTacToeMove) randomMove).getColumn());
        game.doMove(newMove);

        McNode child = new McNode(this, new State(game, newMove));
        childArray.add(child);
        return child;
    }

    public boolean canExpandNode() {
        return state.getUnexploredMoves().size() > 0;
    }

    public void backPropagation(Score score) {
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
            //playerRewards += key + ": " + score.getReward().get(i) + ";";
            playerRewards += String.format("%s: %s", key, score.getScorePlayer((Player) key));
        }

        //String move;

//        if (moveToThisParentNode() == null) {
//            move = "(null)";
//        } else {
//            move = "(" + moveToThisParentNode() + "," + moveUsedToGetToNode.position.y + ")";
//        }
        //System.out.println(spacing + "Player: " + player + " " + move + " Simulations: " + numSimulations + ". Rewards: " + playerRewards);
        System.out.println(String.format("Player: %s, Move: %s, Simulations: %s, Rewards: %s", this.state.getPlayer(), state.moveToParent != null ? state.moveToParent : null, numSims, playerRewards));

        for (Node child : childArray) {
            ((McNode) child).printTree();
        }
    }
}