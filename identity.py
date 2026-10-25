import hashlib
import json
import re
from dataclasses import dataclass

_ALPHABET = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
_CODE_PATTERN = re.compile(r"^[0-9A-Z]{12}$")

#: Board sizes a puzzle code may name. Kept in step with the generator in
#: main.py: a code is regenerated from its seed, so a size the generator
#: cannot build would turn into a code that loads and then fails.
SUPPORTED_SIZES = (4, 6, 8, 9, 10, 12, 15, 16)


def _encode_number(value, length=10):
    value = int(value)
    if value < 0 or value >= 36 ** length:
        raise ValueError("Puzzle seed is too large")
    encoded = []
    for _ in range(length):
        value, remainder = divmod(value, 36)
        encoded.append(_ALPHABET[remainder])
    return "".join(reversed(encoded))


def _decode_number(code, length=12):
    if not isinstance(code, str) or not re.fullmatch(rf"[0-9A-Z]{{{length}}}", code.upper()):
        raise ValueError(f"Puzzle code must contain exactly {length} valid characters")
    value = 0
    for character in code.upper():
        value = value * 36 + _ALPHABET.index(character)
    return value


@dataclass(frozen=True)
class PuzzleIdentity:
    seed: int
    variant: str
    size: int
    box_rows: int
    box_cols: int
    difficulty: str

    def __post_init__(self):
        if not isinstance(self.seed, int) or not 0 <= self.seed < 36 ** 10:
            raise ValueError("Puzzle seed must be a non-negative 10-character code value")
        if self.size not in SUPPORTED_SIZES:
            raise ValueError("Unsupported puzzle size")
        if self.box_rows <= 0 or self.box_cols <= 0 or self.size % self.box_rows or self.size % self.box_cols:
            raise ValueError("Box dimensions must evenly divide the board")
        if not self.variant or not self.difficulty:
            raise ValueError("Variant and difficulty are required")

    @property
    def code(self):
        checksum = self._checksum
        return _encode_number(self.seed) + _encode_number(checksum, 2)

    @property
    def _checksum(self):
        canonical = f"{self.seed}|{self.variant}|{self.size}|{self.box_rows}|{self.box_cols}|{self.difficulty}"
        digest = hashlib.sha256(canonical.encode("utf-8")).digest()
        return int.from_bytes(digest[:4], "big") % (36 ** 2)

    @classmethod
    def create(cls, variant, size, box_rows, box_cols, difficulty, seed=None):
        if seed is None:
            # Folded into the code's own range. SHA-256 gives 2**64 and the
            # constructor rejects anything at or above 36**10, so the default
            # path raised roughly 99.98% of the time and only happened to work
            # when the digest landed small. Both production callers pass `seed=`
            # today, which is the only reason nobody had hit it.
            digest = int.from_bytes(hashlib.sha256(f"{variant}|{size}|{difficulty}".encode()).digest()[:8], "big")
            seed = digest % (36 ** 10)
        return cls(seed, variant, size, box_rows, box_cols, difficulty)

    @classmethod
    def from_code(cls, code, variant, size, box_rows, box_cols, difficulty):
        code = str(code).strip().upper()
        if not _CODE_PATTERN.fullmatch(code):
            raise ValueError("Invalid puzzle code")
        seed = _decode_number(code[:10], 10)
        identity = cls(seed, variant, size, box_rows, box_cols, difficulty)
        if identity.code != code:
            raise ValueError("Puzzle code checksum does not match its settings")
        return identity

    def validate(self, variant=None, size=None, box_rows=None, box_cols=None, difficulty=None):
        expected = {
            "variant": variant,
            "size": size,
            "box_rows": box_rows,
            "box_cols": box_cols,
            "difficulty": difficulty,
        }
        for key, value in expected.items():
            if value is not None and getattr(self, key) != value:
                raise ValueError(f"Puzzle {key} does not match the code")
        return True

    def to_payload(self):
        return {
            "identity_version": 1,
            "seed": self.seed,
            "variant": self.variant,
            "size": self.size,
            "box_rows": self.box_rows,
            "box_cols": self.box_cols,
            "difficulty": self.difficulty,
            "code": self.code,
        }

    @classmethod
    def from_payload(cls, payload):
        if not isinstance(payload, dict) or payload.get("identity_version") != 1:
            raise ValueError("Unsupported puzzle identity payload")
        identity = cls(
            int(payload["seed"]),
            str(payload["variant"]),
            int(payload["size"]),
            int(payload["box_rows"]),
            int(payload["box_cols"]),
            str(payload["difficulty"]),
        )
        if payload.get("code") != identity.code:
            raise ValueError("Puzzle identity code is invalid")
        return identity

    def export_json(self):
        return json.dumps(self.to_payload(), separators=(",", ":"))

    @classmethod
    def import_json(cls, text):
        return cls.from_payload(json.loads(text))
