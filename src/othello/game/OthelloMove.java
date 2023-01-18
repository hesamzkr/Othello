package othello.game;

import java.util.ArrayList;

public class OthelloMove implements Move {
    private Mark mark;
    private int row;
    private int col;

    private Move linkedMove;

    private ArrayList toFlip;

    public OthelloMove(Mark mark, int row, int col) {
        this.mark = mark;
        toFlip = new ArrayList<>();
//        this.index = index;
    }

//    public int getIndex() {
//        return index;
//    }

    public int getRow() {
        return row;
    }

    public int getCol() {
        return col;
    }

    public Move getLinkedMove() {
        return linkedMove;
    }

    public void setLinkedMark(Move move) {
        this.linkedMove = move;
    }

    public void setToFlip(Move move) {
        toFlip.add(move);
    }

    public void addToFlip(ArrayList moves) {
        toFlip.addAll(moves);
    }

    public Mark getMark() {
        return mark;
    }
}
