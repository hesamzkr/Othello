package othello.game;

/**
 * A move in a turn-based game.
 */
public interface Move {
    /**
     * Getter for row of move
     *
     * @return row of the move
     */
    int getRow();

    /**
     * Getter for column of move
     *
     * @return column of the move
     */
    int getCol();

    /**
     * Getter for the mark of move
     *
     * @return mark of the move
     */
    Mark getMark();

    /**
     * Getter for the index of the move
     *
     * @return move's index
     */
    int getIndex();
}
