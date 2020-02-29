import gamelib
import random
import math
import warnings
from sys import maxsize
import json


"""
Most of the algo code you write will be in this file unless you create new
modules yourself. Start by modifying the 'on_turn' function.

Advanced strategy tips:

  - You can analyze action frames by modifying on_action_frame function

  - The GameState.map object can be manually manipulated to create hypothetical
  board states. Though, we recommended making a copy of the map to preserve
  the actual current map state.
"""

class AlgoStrategy(gamelib.AlgoCore):
    def __init__(self):
        super().__init__()
        seed = random.randrange(maxsize)
        random.seed(seed)
        gamelib.debug_write('Random seed: {}'.format(seed))

    def on_game_start(self, config):
        """
        Read in config and perform any initial setup here
        """
        gamelib.debug_write('Configuring your custom algo strategy...')
        self.config = config
        global FILTER, ENCRYPTOR, DESTRUCTOR, PING, EMP, SCRAMBLER, BITS, CORES, PLAYER, ENEMY
        FILTER = config["unitInformation"][0]["shorthand"]
        ENCRYPTOR = config["unitInformation"][1]["shorthand"]
        DESTRUCTOR = config["unitInformation"][2]["shorthand"]
        PING = config["unitInformation"][3]["shorthand"]
        EMP = config["unitInformation"][4]["shorthand"]
        SCRAMBLER = config["unitInformation"][5]["shorthand"]
        BITS = 1
        CORES = 0
        PLAYER = 0
        ENEMY = 1
        # This is a good place to do initial setup
        self.scored_on_locations = []
        self.spawn_points = [[15,1], [16,2]]
        # self.destructor_locations = [[0, 13], [26, 12], [5, 11], [6, 11]]
        # self.encryptor_locations = [[14, 2], [4, 9], [5, 8]]
        # self.filter_locations = [[26, 13], [27, 13], [25, 12], \
        #  [25, 11], [24, 10], [23, 9], [8, 8], [22, 8], [9, 7], [21, 7], [10, 6], \
        #  [20, 6], [11, 5], [19, 5], [12, 4], [18, 4], [13, 3], [15, 3], [16, 3], [17, 3]]
        # self.extra_destructor = [[1,12], [2,11], [4,12], [6,10], [5,12], [6,12]]
        # self.non_essential =[[7, 9], [6, 10], [1, 12], [4, 12], [2, 11]]

        self.priority1 = [None] * 3
        self.priority1[0] = [[27, 13], [26, 12], [25, 11], [7, 10], [24, 10], \
            [8, 9], [23, 9], [9, 8], [22, 8], [10, 7], \
            [21, 7], [11, 6], [20, 6], [12, 5], [19, 5], [13, 4], [18, 4],  \
            [14, 3], [15, 3], [16, 3], [17, 3]]
        self.priority1[1] = [[0, 13], [25, 12], [5, 11], [6, 11]]
        self.priority1[2] = [[14, 2]]

        self.priority2 = [None] * 3
        self.priority2[0] = [[1, 13], [2, 12], [6, 12], [7, 12], [8, 11], [9, 10], [10, 9], [10, 8]]
        self.priority2[1] = [[1, 12], [4, 12], [5, 12], [2, 11], [4, 11], \
            [7, 11], [6, 10], [8, 10], [7, 9], [9, 9], [8, 8]]

        self.priority3 = [None] * 3
        self.priority3[0] = [[20, 13], [21, 13], [22, 13], [23, 13], [24, 13], \
            [25, 13], [26, 13], [20, 12], [21, 12], [20, 11], [20, 10]]
        self.priority3[1] = [[22, 12]]

        self.priority5 = [None] * 3
        self.priority5[2] = [[5, 10], [6, 9], [7, 8], [8, 7], [9, 6]]

        self.priority4 = [None] * 5
        self.priority4[0] = [[24, 12], [22, 11], [21, 10]]
        self.priority4[1] = [[23, 12], [21, 11], [23, 11], [24, 11], [22, 10]]

        self.total_defense_locations = [self.priority1, self.priority2, self.priority3, self.priority4, self.priority5]

        self.num_destructors = 0

        self.upgrade_location = [[1,13], [2,12], [27, 13]]

        self.SCRAMBLERS_PER_BIT = 5
        self.MIN_BITS_SPENT_ATTACK = 6
        self.scored_on_locations = []
        self.attacks_on_frame = [0] * 14
        self.bits_to_enemy_attack = dict()

    def on_turn(self, turn_state):
        """
        This function is called every turn with the game state wrapper as
        an argument. The wrapper stores the state of the arena and has methods
        for querying its state, allocating your current resources as planned
        unit deployments, and transmitting your intended deployments to the
        game engine.
        """
        game_state = gamelib.GameState(self.config, turn_state)
        gamelib.debug_write('Performing turn {} of your custom algo strategy'.format(game_state.turn_number))
        game_state.suppress_warnings(True)  #Comment or remove this line to enable warnings.

        self.unit_counted = dict()
        self.starter_strategy(game_state)

        game_state.submit_turn()


    """
    NOTE: All the methods after this point are part of the sample starter-algo
    strategy and can safely be replaced for your custom algo.
    """

    def starter_strategy(self, game_state):

        """
        For defense we will use a spread out layout and some Scramblers early on.
        We will place destructors near locations the opponent managed to score on.
        For offense we will use long range EMPs if they place stationary units near the enemy's front.
        If there are no stationary units to attack in the front, we will send Pings to try and score quickly.
        """
        self.num_destructors = self.detect_destructors(game_state)
        self.reprioritize(game_state)
        self.build_defences(game_state)
        self.upgrade_defences(game_state)
        self.place_scramblers(game_state)
        self.send_ping_squadron(game_state)

    def place_scramblers(self, game_state):
        """
        Predict enemy attack to place appropiately many scramblers
        """

        def index_to_location(index):
            return [index + 1, 13 - index - 1]

        if not self.attack_predicted(game_state): return

        ls = self.attacks_on_frame.copy()
        total = sum(ls)
        num = int(self.enemy_bits / self.SCRAMBLERS_PER_BIT)
        for _ in range(num):
            i = ls.index(max(ls))
            ls[i] -= total / num
            game_state.attempt_spawn(SCRAMBLER, index_to_location(i))


    def attack_predicted(self, game_state):
        self.enemy_bits = game_state.get_resource(BITS, ENEMY)
        diff = 0
        for bits, attacked in self.bits_to_enemy_attack.items():
            if self.enemy_bits > bits and attacked:
                diff += 1
            elif self.enemy_bits < bits and not attacked:
                diff -= 1
        return diff > 0

    def reprioritize(self, game_state):

        countLeft = 0
        countRight = 0

        num_survey = -3
        if len(self.scored_on_locations) < 3:
            num_survey = -len(self.scored_on_locations)

        for location in self.scored_on_locations[num_survey:]:
            if location[0] <= 13:
                countLeft += 1
            else:
                countRight += 1

        if countRight > countLeft:
            self.swap_priority(1, 3)
            self.swap_priority(3, 2)


    def upgrade_defences(self, game_state):

        for location in self.upgrade_location:
            game_state.attempt_upgrade(location)

    def build_defences(self, game_state):

        num_cores = game_state.get_resource(CORES)

        for kk in range(len(self.total_defense_locations)):
            if kk >= 2 and self.num_destructors < 15:
                break
            if kk >= 1 and game_state.get_resource(CORES) < 6:
                return
            for ii in range(len(self.total_defense_locations[kk])):
                if self.total_defense_locations[kk][ii] == None:
                    continue
                for location in self.total_defense_locations[kk][ii]:
                    if ii == 0:
                        game_state.attempt_spawn(FILTER, location)
                        num_cores -= gamelib.GameUnit(FILTER, game_state.config).cost[game_state.CORES]
                    elif ii == 1:
                        game_state.attempt_spawn(DESTRUCTOR, location)
                        num_cores -= gamelib.GameUnit(DESTRUCTOR, game_state.config).cost[game_state.CORES]
                    else:
                        game_state.attempt_spawn(ENCRYPTOR, location)
                        num_cores -= gamelib.GameUnit(ENCRYPTOR, game_state.config).cost[game_state.CORES]


    def send_ping_squadron(self, game_state):
        # Send pings.
        if game_state.get_resource(BITS) / gamelib.GameUnit(PING, game_state.config).cost[game_state.BITS] >= 18:
                game_state.attempt_spawn(PING, self.spawn_points[0], 8)
                game_state.attempt_spawn(PING, self.spawn_points[1], 1000)

    def detect_destructors(self, game_state):
        total_units = 0
        for location in game_state.game_map:
            if game_state.contains_stationary_unit(location):
                for unit in game_state.game_map[location]:
                    if unit.player_index == 0 and unit.unit_type == DESTRUCTOR:
                        total_units += 1
        return total_units

    def swap_priority(self, p1, p2):
        temp = self.total_defense_locations[p1]
        self.total_defense_locations[p1] = self.total_defense_locations[p2]
        self.total_defense_locations[p2] = temp

    def on_action_frame(self, turn_string):
        """
        This is the action frame of the game. This function could be called
        hundreds of times per turn and could slow the algo down so avoid putting slow code here.
        Processing the action frames is complicated so we only suggest it if you have time and experience.
        Full doc on format of a game frame at: https://docs.c1games.com/json-docs.html
        """
        # Let's record at what position we get scored on
        state = json.loads(turn_string)
        events = state["events"]
        breaches = events["breach"]

        P2 = 2

        frame = state['turnInfo'][2]
        for attack in events['attack']:
            # first attack by enemy ping or emp
            if attack[6] == P2 and (attack[3] == 3 or attack[3] == 4) and attack[4] not in self.unit_counted:
                # onto player's left side
                if attack[1][1] <= 13 and attack[1][0] <= 13 and frame // 8 < len(self.attacks_on_frame):
                    self.attacks_on_frame[frame // 8] += 1
                    self.unit_counted[attack[4]] = True
        if len(events['spawn']) > 0:
            spent = 0
            for spawn in events['spawn']:
                if spawn[3] == P2:
                    if spawn[1] == 3: spent += 1
                    if spawn[1] == 4: spent += 3
            if spent >= self.MIN_BITS_SPENT_ATTACK:
                self.bits_to_enemy_attack[self.enemy_bits] = True
            else:
                self.bits_to_enemy_attack[self.enemy_bits] = False


        for breach in breaches:
            location = breach[0]
            unit_owner_self = True if breach[4] == 1 else False
            # When parsing the frame data directly,
            # 1 is integer for yourself, 2 is opponent (StarterKit code uses 0, 1 as player_index instead)
            if not unit_owner_self:
                gamelib.debug_write("Got scored on at: {}".format(location))
                self.scored_on_locations.append(location)
                gamelib.debug_write("All locations: {}".format(self.scored_on_locations))



if __name__ == "__main__":
    algo = AlgoStrategy()
    algo.start()
