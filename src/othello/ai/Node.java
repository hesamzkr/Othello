package othello.ai;

import othello.game.Player;

import java.util.List;

/**
 * An interface for a node in a search tree.
 */
public interface Node {

    /**
     * Gets the parent of a node.
     *
     * @return the parent node.
     */
    Node getParent();

    /**
     * Gets the state of a node
     *
     * @return the state of a node.
     */
    State getState();

    /**
     * Gets the child array of a node
     *
     * @return a list of child nodes.
     */
    List<Node> getChildArray();

    /**
     * Gets the score for a player.
     *
     * @param player who's score should be retrieved.
     * @return the score for the selected player.
     */
    double getScoreForPlayer(Player player);
}
