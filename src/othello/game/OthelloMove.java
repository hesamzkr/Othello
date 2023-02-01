package othello.game;

import java.util.ArrayList;
import java.util.List;

public class OthelloMove implements Move {
    private final Mark mark;
    private final int row;
    private final int col;

    private final List<OthelloMove> toFlip;

    /**
     * Constructor for a move of Othello with the row, column and mark specified.
     * It initializes toFlip
     *
     * @param mark of the move
     * @param row  of the move
     * @param col  column of the move
     */
    public OthelloMove(Mark mark, int row, int col) {
        this.row = row;
        this.col = col;
        this.mark = mark;
        toFlip = new ArrayList<>();
    }

    /**
     * Returns the row of the move
     *
     * @return move's row
     */
    public int getRow() {
        return row;
    }

    /**
     * Returns the column of the move
     *
     * @return move's column
     */
    public int getCol() {
        return col;
    }

    /**
     * Calculates and returns the index of move
     *
     * @return move's index
     */
    public int getIndex() {
        return row * Board.DIM + col;
    }

    /**
     * Adds all the pieces that should be flipped to this move.
     *
     * @param moves a list of moves for the pieces that should be flipped.
     */
    public void addToFlip(List<OthelloMove> moves) {
        toFlip.addAll(moves);
    }

    /**
     * Gets all the moves that flip certain pieces.
     *
     * @return a list of moves for the pieces that should be flipped.
     */
    public List<OthelloMove> getToFlip() {
        return toFlip;
    }

    /**
     * Returns the mark of the move
     *
     * @return move's mark
     */
    public Mark getMark() {
        return mark;
    }
}
