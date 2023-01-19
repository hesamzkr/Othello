package othello.game;

/**
 * A player of a turn-based game.
 */
public interface Player {
    String getName();

    Mark getMark();

    void setMark(Mark mark);

    Move determineMove(Game game);
}
