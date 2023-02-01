package othello.game;

import java.util.List;

/**
 * A player of a turn-based game.
 */
public interface Player {
    /**
     * Returns the name of the player
     *
     * @return name of player
     */
    String getName();

    /**
     * Returns the mark of the player
     *
     * @return mark of player
     */
    Mark getMark();

    /**
     * Setter for player's mark
     *
     * @param mark to be set for player
     */
    void setMark(Mark mark);

    /**
     * The player chooses a list of moves from the valid moves it
     * can choose and returns it
     *
     * @param game player is playing in
     * @return list of moves that the player has chosen to make
     * @throws NoValidMovesException Exception for when the player has no valid moves to make
     */
    List<Move> determineMove(Game game) throws NoValidMovesException;
}
