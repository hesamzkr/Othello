package othello.ai;

import othello.game.Game;
import othello.game.Move;
import othello.game.OthelloGame;
import othello.game.Player;

import java.util.List;

/**
 * Stores the current state of the game, as well as store information related to a node such as which move was played to get to the game state of its parent.
 */
public class State {
    private Game game;
    private Player player;

    /**
     * Should only be accessed by other classes in this package, such as the McNode class.
     */
    protected List<Move> moveToParent;

    private List<Move> unexploredMoves;

    /**
     * Which locations on the board can be played move by the player.
     */
    private List<int[]> validIndices;


    public State(Game game, List<Move> moveToParent) {
        this.moveToParent = moveToParent;
        this.game = game;
        if (game != null) { //In order to get the following fields, ensure that the game is not null.
            this.unexploredMoves = game.getValidMoves(game.getTurn().getMark());
            this.validIndices = ((OthelloGame) game).showValids(unexploredMoves);
            this.player = game.getTurn();
        }
    }

    /**
     * Gets the game.
     *
     * @return the game.
     */
    public Game getGame() {
        return game;
    }

    /**
     * Gets the player who has the turn for this game state.
     *
     * @return the current player.
     */
    public Player getPlayer() {
        return player;
    }

    /**
     * Get the valid moves that not have been explored yet.
     *
     * @return a list of moves.
     */
    public List<Move> getUnexploredMoves() {
        return unexploredMoves;
    }

    /**
     * Gets the row and column of the locations that can be played.
     *
     * @return a list of row/column pairs that.
     */
    public List<int[]> getValidIndices() {
        return validIndices;
    }
}
