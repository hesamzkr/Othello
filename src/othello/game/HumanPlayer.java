package othello.game;

import java.util.List;

/**
 * Player for a game which chooses the moves through user input
 */
public class HumanPlayer extends AbstractPlayer {

    /**
     * Constructor which takes in user's name
     *
     * @param name player's name
     */
    public HumanPlayer(String name) {
        super(name);
    }

    /**
     * Not used for HumanPlayer as the TUI is complex and is being handled on its own through the use of menus.
     * This function is simply here so it can be an AbstractPlayer
     */
    @Override
    public List<Move> determineMove(Game game) throws NoValidMovesException {
        return null;
    }

    /**
     * Set the mark of player
     *
     * @param m to be set for player
     */
    public void setMark(Mark m) { //Clean: is this useless?
        super.mark = m;
    }
}
