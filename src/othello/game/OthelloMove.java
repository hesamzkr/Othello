package othello.game;

import java.util.ArrayList;
import java.util.List;

public class OthelloMove implements Move {
    private final Mark mark;
    private final int row;
    private final int col;

    private final List<OthelloMove> toFlip;

    public OthelloMove(Mark mark, int row, int col) {
        this.row = row;
        this.col = col;
        this.mark = mark;
        toFlip = new ArrayList<>();
    }

    public int getRow() {
        return row;
    }

    public int getCol() {
        return col;
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

    public Mark getMark() {
        return mark;
    }
}
