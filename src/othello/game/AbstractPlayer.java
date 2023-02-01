package othello.game;

import java.util.List;

/**
 * A player of a game.
 */
public abstract class AbstractPlayer implements Player {
    private final String name;
    protected Mark mark;

    /**
     * Creates a new Player object.
     */
    /*@ requires name != null;
        ensures getName() == name;
    @*/
    public AbstractPlayer(String name) {
        this.name = name;
    }

    /**
     * Gets the name of a player
     *
     * @return string of the player's name.
     */
    public String getName() {
        return name;
    }

    /**
     * Gets the mark of a player.
     *
     * @return the mark of a player.
     */
    public Mark getMark() {
        return mark;
    }

    public void setMark(Mark mark) {
        this.mark = mark;
    }

    /**
     * Determines the next move, if the game still has available moves.
     *
     * @param game the current game
     * @return the player's choice
     */
    //@ requires !game.isGameover();
    //@ ensures game.isValidMove(\result);
    public abstract List<Move> determineMove(Game game) throws NoValidMovesException;

    /**
     * Returns a representation of a player, i.e., their name
     *
     * @return the String representation of this object
     */
    @Override
    public String toString() {
        return "Player " + name;
    }
}
