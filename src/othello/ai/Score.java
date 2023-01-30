package othello.ai;

import othello.game.Player;

import java.util.HashMap;
import java.util.Map;

public class Score {
    Map<Player, Double> scores = new HashMap<>();

    public Score(Player player1, Player player2, double scorePlayer1, double scorePlayer2) {
        scores.put(player1, scorePlayer1);
        scores.put(player2, scorePlayer2);
    }

    public Map<Player, Double> getScores() {
        return scores;
    }

    public double getScorePlayer(Player player) {
        return scores.get(player);
    }


    public void incScore(Score score) {
        for (var keys : score.getScores().keySet()) {
            scores.put(keys, scores.get(keys) + score.getScorePlayer(keys));
        }
    }
}
