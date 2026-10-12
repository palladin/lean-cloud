import Fixture.Left
import Fixture.Right
namespace Fixture

theorem result : twice 1 + twice 2 = 6 := by rw [left, right]
