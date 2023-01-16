package othello.game;

public class TicTacToeMove implements Move {
    private Mark mark;
    private int row;
    private int column;

    public TicTacToeMove(Mark mark, int row, int column) {
        this.mark = mark;
        this.row = row;
        this.column = column;
    }

    public int getRow() {
        return row;
    }

    public int getColumn() {
        return column;
    }

    public Mark getMark() {
        return mark;
    }
}
