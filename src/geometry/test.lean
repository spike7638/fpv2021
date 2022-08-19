import tactic
import data.real.basic

example: ∃ t, 4 = t * 4 :=
begin
have hex: 4 = 1 * 4 := by linarith,
exact exists.intro 1 hex
end