package othello.ai;

import othello.game.Player;

import java.util.HashMap;
import java.util.Map;

public class Score {
    Map scores = new HashMap<Player, Integer>();

//    public Score(int scorePlayer1, int scorePlayer2) {
//        scores.put("Player1", scorePlayer1);
//        scores.put("Player2", scorePlayer2);
//
//    }

    public Score(Player player1, Player player2, int scorePlayer1, int scorePlayer2) {
        scores.put(player1, scorePlayer1);
        scores.put(player2, scorePlayer2);
    }

    public Map getScores() {
        return scores;
    }

    public int getScorePlayer(Player player) {
        return (int) scores.get(player);
    }

//    public int getRewardPlayer1() {
//        return (int) scores.get("Player1");
//    }
//
//    public int getRewardPlayer2() {
//        return (int) scores.get("Player2");
//    }
//
//    public void increaseScore(Score score) {
//        scores.put("Player1", score.getRewardPlayer1());
//        scores.put("Player2", score.getRewardPlayer2());

    public void incScore(Score score) {
        for (var keys : score.getScores().keySet()) {
            scores.put(keys, (int) scores.get(keys) + score.getScorePlayer((Player) keys));
        }
    }
}
