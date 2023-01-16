package tictactoe.ai;

import tictactoe.model.Game;
import tictactoe.model.Move;
import tictactoe.model.TicTacToeGame;

public class MonteCarloStrategy implements Strategy {

    private int numIterations;

    public MonteCarloStrategy(Difficulty difficulty) {
        switch (difficulty) {
            case EASY -> numIterations = 20;
            case MEDIUM -> numIterations = 2000;
            case HARD -> numIterations = 10000;
        }
    }

    @Override
    public String getName() {
        return "Monte Carlo Tree Search ";
    }

    @Override
    public Move determineMove(Game game) {
        Node root = new McNode(null, new State(game, null));
        for (int i = 0; i < numIterations; i++) {
            Game newGame = game.deepCopy();
            Node newNode = select(root, newGame);
            newNode = ((McNode) newNode).expandNode((TicTacToeGame) newGame);
            Score score = simulate(newGame);
            ((McNode) newNode).backPropagation(score);
        }

        Node childWithMostVisits = ((McNode) root).getNodeWithMostVisits();
        return ((McNode) childWithMostVisits).getState().moveToParent;
    }

    /**
     * Takes an existing game and should simulate how it plays out using random players
     *
     * @param newGame
     * @return
     */
    private Score simulate(Game newGame) {
        while (!newGame.isGameover()) {
            newGame.doMove(new NaiveStrategy().determineMove(newGame));
            ((TicTacToeGame) newGame).nextTurn();
        }
        return ((TicTacToeGame) newGame).getScores();
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
        boolean condition2 = newGame.isGameover();
        while (((McNode) node).canExpandNode() == false && newGame.isGameover() == false) {
            node = ((McNode) node).selectNode();
            Move move = ((McNode) node).getState().moveToParent;
            //System.out.println(move);
            if (move != null) {
                newGame.doMove(move);
                ((TicTacToeGame) newGame).nextTurn();
            }
        }
        return node;
    }


}
