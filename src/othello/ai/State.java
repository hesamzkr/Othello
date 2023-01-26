package othello.ai;

import othello.game.Game;
import othello.game.Move;
import othello.game.OthelloGame;
import othello.game.Player;

import java.util.List;

public class State {
    private Game game;
    private Player player;

    public List<Move> moveToParent;

    private List<Move> unexploredMoves;

    private List<int[]> validIndices;

    /**
     * setting the player (or AI) as opponent should allow it to also
     * recommend moves to the player.
     *
     * @param game
     */
    public State(Game game, List<Move> moveToParent) {
        this.moveToParent = moveToParent;
        this.game = game; //deepcopy?
//        this.unexploredMoves = game.getValidMoves(game.getTurn().getMark());
//        this.validIndices = ((OthelloGame) game).showValids();
//        this.player = game.getTurn(); //change later
        if (game != null) {
            this.unexploredMoves = game.getValidMoves(game.getTurn().getMark());
            this.validIndices = ((OthelloGame) game).showValids();
            this.player = game.getTurn(); //change later
        }
    }

    public Game getGame() {
        return game;
    }

    public Player getPlayer() {
        return player;
    }

//    public void randomMove() {
//        NaiveStrategy strat = new NaiveStrategy();
//        game.doMove(strat.determineMove(game));
//    }

    public Move getMoveToParent() {
        return getMoveToParent();
    }


    public List<Move> getUnexploredMoves() {
        return unexploredMoves;
    }

    public List<int[]> getValidIndices() {
        return validIndices;
    }
}
