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

    public void addToFlip(List<OthelloMove> moves) {
        toFlip.addAll(moves);
    }

    public List<OthelloMove> getToFlip() {
        return toFlip;
    }

    public Mark getMark() {
        return mark;
    }
}
