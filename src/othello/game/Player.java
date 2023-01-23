package othello.game;

import java.util.List;

/**
 * A player of a turn-based game.
 */
public interface Player {
    String getName();

    Mark getMark();

    void setMark(Mark mark);

    List<Move> determineMove(Game game) throws NoValidMoves;
}
