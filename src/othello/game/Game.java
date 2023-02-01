package othello.game;

import java.util.List;

/**
 * A simple turn-based game.
 */
public interface Game {
    /**
     * Check if the game is over, i.e., there is a winner or no more moves are available.
     *
     * @return whether the game is over
     */
    boolean isGameOver();

    /**
     * Query whose turn it is
     *
     * @return the player whose turn it is
     */
    Player getTurn();

    /**
     * Get the winner of the game. If the game is a draw, then this method returns null.
     *
     * @return the winner, or null if no player is the winner
     */
    Player getWinner();

    /**
     * Return all moves that are valid in the current state of the game
     *
     * @return the list of currently valid moves
     */
    List<Move> getValidMoves(Mark m);

    /**
     * Perform the move, assuming it is a valid move.
     *
     * @param move the move to play
     */
    void doMove(List<Move> move);

    /**
     * Creates a new instance of game with
     * same state and returns it
     *
     * @return a copy of the game.
     */
    Game deepCopy();

    /**
     * Getter for board
     *
     * @return game board
     */
    Board getBoard();
}
