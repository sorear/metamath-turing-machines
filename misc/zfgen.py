axioms = {
    'ax-1': '( ph -> ( ps -> ph ) )',
    'ax-2': '( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )',
    'ax-3': '( ( -. ph -> -. ps ) -> ( ps -> ph ) )',
    'ax-mp': {
        'e': ['ph', '( ph -> ps )'],
        'a': 'ps',
    },
    'ax-4': '( A. x ph -> ph )',
    'ax-5': '( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) )',
    'ax-6': '( -. A. x ph -> A. x -. A. x ph )',
    'ax-7': '( A. x A. y ph -> A. y A. x ph )',
    'ax-gen': {
        'e': ['ph'],
        'a': 'A. x ph',
    },
    'ax-8': '( x = y -> ( x = z -> y = z ) )',
    'ax-9': '-. A. x -. x = y',
    'ax-10': '( A. x x = y -> A. y y = x )',
    'ax-11': '( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) )',
    'ax-12o': '( -. A. z z = x -> ( -. A. z z = y -> ( x = y -> A. z x = y ) ) )',
    'ax-13': '( x = y -> ( x e. z -> y e. z ) )',
    'ax-14': '( x = y -> ( z e. x -> z e. y ) )',
    'ax-15': '( -. A. z z = x -> ( -. A. z z = y -> ( x e. y -> A. z x e. y ) ) )',
    'ax-16': {
        'd': 'x y',
        'a': '( A. x x = y -> ( ph -> A. x ph ) )',
    },
    'ax-ext': {
        'd': 'x y z',
        'a': '( A. z ( z e. x <-> z e. y ) -> x = y )',
    },
    'ax-rep': {
        'd': 'x y z w',
        'a': r'( A. w E. y A. z ( A. y ph -> z = y ) -> E. y A. z ( z e. y <-> E. w ( w e. x /\ A. y ph ) ) )',
    },
    'ax-pow': {
        'd': 'x y z w',
        'a': 'E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y )',
    },
    'ax-un': {
        'd': 'x y z w',
        'a': r'E. y A. z ( E. w ( z e. w /\ w e. x ) -> z e. y )',
    },
    'ax-inf2': {
        'd': 'x y z w',
        'a': r'E. x ( E. y ( y e. x /\ A. z -. z e. y ) /\ A. y ( y e. x -> E. z ( z e. x /\ A. w ( w e. z <-> ( w e. y \/ w = y ) ) ) ) )',
    },
}

# let's target a random higher set theory result, gchac:
# this is edited from "SHOW TRACE_BACK .../mat ax-*/ax" output
derivable = {
    'gchac': 'ax-1 ax-2 ax-3 ax-mp ax-5 ax-6 ax-7 ax-gen ax-8 ax-11 ax-13 ax-14 ax-17 ax-12o ax-10 ax-9 ax-4 ax-16 ax-ext ax-rep ax-sep ax-nul ax-pow ax-pr ax-un ax-inf2',
    'ax-pr': 'ax-1 ax-2 ax-3 ax-mp ax-5 ax-6 ax-7 ax-gen ax-8 ax-11 ax-14 ax-17 ax-12o ax-10 ax-9 ax-4 ax-16 ax-ext ax-rep ax-sep ax-nul ax-pow', # axpr
    'ax-17': 'hbim hbn hbal ax17eq ax17el', # metatheorem
    'hbal': 'ax-1 ax-2 ax-mp ax-5 ax-7 ax-gen',
    'hbn': 'ax-1 ax-2 ax-3 ax-mp ax-5 ax-6 ax-gen ax-4',
    'hbim': 'ax-1 ax-2 ax-3 ax-mp ax-5 ax-6 ax-gen ax-4',
    'ax17eq': 'ax-1 ax-2 ax-3 ax-mp ax-12o ax-16',
    'ax17el': 'ax-1 ax-2 ax-3 ax-mp ax-16 ax-15',
    'ax-sep': 'ax-1 ax-2 ax-3 ax-mp ax-5 ax-6 ax-7 ax-gen ax-8 ax-13 ax-14 ax-17 ax-9 ax-4 ax-rep', # axsep
    'ax-nul': 'ax-1 ax-2 ax-3 ax-mp ax-5 ax-gen ax-sep', # axnul
}
# ax-4, ax-10, ax-11, ax-12o are proven redundant in systems that include ax-17

derived = set()
def assert_derivable(name):
    if name in derived or name in axioms:
        return
    if name not in derivable:
        raise RuntimeError(name + ' not axiom or derivable')
    for hypot in derivable[name].split(' '):
        assert_derivable(hypot)
    derived.add(name)

assert_derivable('gchac')

rules = {
    'WFF': {
        'wph': 'ph',
        'wps': 'ps',
        'wch': 'ch',
        'weq': 'SET = SET',
        'wel': 'SET e. SET',
        'wi': '( WFF -> WFF )',
        'wn': '-. WFF',
        'wo': r'( WFF \/ WFF )',
        'wa': r'( WFF /\ WFF )',
        'wb': '( WFF <-> WFF )',
        'wal': 'A. SET WFF',
        'wex': 'E. SET WFF',
    },
    'SET': {
        'vx': 'x',
        'vy': 'y',
        'vz': 'z',
        'vw': 'w',
    }
}

def parse_wff(string):
    tokens = string.split(' ')
    packrat = {}

    def cached(cat, index):
        if (cat, index) not in packrat:
            packrat[(cat, index)] = recurse(cat, index)
        return packrat[(cat, index)]

    def recurse(cat, index):
        for rule, rulestr in rules[cat].items():
            cursor = index
            for token in rulestr.split(' '):
                if token in rules:
                    subparse = cached(token, cursor)
                    ...
                else:
