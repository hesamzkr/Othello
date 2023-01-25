package othello.ai;

import othello.game.*;

import java.util.List;

public class MonteCarloStrategy implements Strategy {

    private int numIterations;

    public MonteCarloStrategy(Difficulty difficulty) {
        switch (difficulty) {
            case EASY -> numIterations = 100;
            case MEDIUM -> numIterations = 1600;
            case HARD -> numIterations = 30000;
        }
    }

    @Override
    public String getName() {
        return "Monte Carlo Tree Search ";
    }

    @Override
    public List<Move> determineMove(Game game) {
        Node root = new McNode(null, new State(game, null));
        for (int i = 0; i < numIterations; i++) {
            Game newGame = game.deepCopy();
            Node newNode = select(root, newGame);
            newNode = ((McNode) newNode).expandNode((OthelloGame) newGame);
            Score score = simulate(newGame);
            ((McNode) newNode).backPropagation(score);
        }

        Node childWithMostVisits = ((McNode) root).getNodeWithMostVisits();
        return childWithMostVisits.getState().moveToParent;
    }

    /**
     * Takes an existing game and should simulate how it plays out using random players
     *
     * @param newGame
     * @return
     */
    private Score simulate(Game newGame) {
        while (!newGame.isGameOver()) {
//            try {
//                newGame.doMove(new NaiveStrategy().determineMove(newGame));
//            } catch (NoValidMoves ignored) {
//            }
//            ((OthelloGame) newGame).nextTurn();
            try {
                Mark current = newGame.getTurn().getMark();
                if (newGame.getValidMoves(current).isEmpty()) {
                    throw new NoValidMoves();
                }
                newGame.doMove(new NaiveStrategy().determineMove(newGame));
            } catch (NoValidMoves ignored) {
            }
            ((OthelloGame) newGame).nextTurn();
        }
        return ((OthelloGame) newGame).getScores();
    }

    /**
     * Traverses through the tree -> make sure that same moves were played to get to these nodes
     * MctsNode rootNode = new MctsNode(null, null, game);
     * <p>
     * public MctsNode(MctsNode parent, TicTacToeMove move, TicTacToeGame game) {
     * this.parent = parent;
     * moveUsedToGetToNode = move;
     * unexploredMoves = game.getAvailableMoves();
     * reward = new Reward(0, 0);
     * player = game.getPlayerToMove();
     * }
     *
     * @param node
     * @param newGame
     * @return
     */
    private Node select(Node node, Game newGame) {
        boolean condition1 = ((McNode) node).canExpandNode();
        boolean condition2 = newGame.isGameOver();
        while (!((McNode) node).canExpandNode() && !newGame.isGameOver()) {
            node = ((McNode) node).selectNode();
            List<Move> move = ((McNode) node).getState().moveToParent;
            if (move != null && move.size() > 0) { //was first != null
                newGame.doMove(move);
                ((OthelloGame) newGame).nextTurn();
            }
        }
        return node;
    }


}
