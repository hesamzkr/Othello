package othello.ai;

import othello.game.Player;

import java.util.HashMap;
import java.util.Map;

/**
 * Manages the score of players after a game.
 */
public class Score {
    Map<Player, Double> scores = new HashMap<>();

    public Score(Player player1, Player player2, double scorePlayer1, double scorePlayer2) {
        scores.put(player1, scorePlayer1);
        scores.put(player2, scorePlayer2);
    }

    /**
     * Gets the scores.
     *
     * @return a map of scores for both players.
     */
    public Map<Player, Double> getScores() {
        return scores;
    }

    /**
     * Gets the score for a certain player.
     *
     * @param player the player for whom the score should be retrieved.
     * @return a double which is the score of the selected player.
     */
    public double getScorePlayer(Player player) {
        return scores.get(player);
    }

    /**
     * Updates the scores of the players.
     *
     * @param score that should be added to the current scores.
     */
    public void incScore(Score score) {
        for (var keys : score.getScores().keySet()) { //The keys are the players.
            scores.put(keys, scores.get(keys) + score.getScorePlayer(keys));
        }
    }
}
