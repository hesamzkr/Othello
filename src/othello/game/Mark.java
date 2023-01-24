package othello.game;

/**
 * Represents a mark in the Tic Tac Toe game. There three possible values:
 * Mark.BB, Mark.WW and Mark.EMPTY.
 * Module 2 lab assignment
 */
public enum Mark {

    EMPTY, BLACK, WHITE, VALID;

    /**
     * Returns the other mark.
     *
     * @return the other mark if this mark is not EMPTY or EMPTY
     */
    //@ requires this != VALID;
    //@ ensures this == BLACK ==> \result == WHITE && this == WHITE ==> \result == BLACK;
    public Mark other() {
        if (this == BLACK) {
            return WHITE;
        } else if (this == WHITE) {
            return BLACK;
        } else {
            return EMPTY;
        }
    }
}
