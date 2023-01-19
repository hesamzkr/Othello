package othello.game;

import java.util.List;

/**
 * A simple turn-based game.
 */
public interface Game {
    //@ public invariant !isGameOver() ==> getValidMoves(Mark.BLACK).size() > 0;
    //@ public invariant !isGameOver() ==> getWinner() == null;
    //@ public invariant !isGameOver() ==> getTurn() != null;

    /**
     * Check if the game is over, i.e., there is a winner or no more moves are available.
     *
     * @return whether the game is over
     */
    //@ pure;
    boolean isGameOver();

    /**
     * Query whose turn it is
     *
     * @return the player whose turn it is
     */
    //@ pure;
    Player getTurn();

    /**
     * Get the winner of the game. If the game is a draw, then this method returns null.
     *
     * @return the winner, or null if no player is the winner
     */
    //@ pure;
    Player getWinner();

    /**
     * Return all moves that are valid in the current state of the game
     *
     * @return the list of currently valid moves
     */
    //@ pure;
    List<Move> getValidMoves(Mark m);

    /**
     * Perform the move, assuming it is a valid move.
     *
     * @param move the move to play
     */
    //@ pure;
    void doMove(Move move);

    Game deepCopy();
}
