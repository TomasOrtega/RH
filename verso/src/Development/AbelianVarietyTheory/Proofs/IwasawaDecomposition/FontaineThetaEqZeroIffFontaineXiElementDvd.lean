import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import ReciprocityTheory.DualLattices.Imports

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

/- English proof (translation)
Establish `hp : ((frobeniusEquiv (Per.Fl l) l).symm e).untilt ^ l = 1`. Rewrite using `[← map_pow, frobeniusEquiv_symm_pow_p, h.1]`. Establish `ho` using `orderOf_eq_prime hp h.2`. Use `IsPrimitiveRoot.orderOf ((frobeniusEquiv (Per.Fl l) l).symm e).untilt` as an intermediate fact. Rewrite `this` using `[ho]`. Then use the resulting hypothesis.
-/
theorem IsEps.isPrimitiveRoot_untilt {l : ℕ} [hl : Fact l.Prime] {e : Per.Fl l} (h : IsEps e) :
    IsPrimitiveRoot ((frobeniusEquiv (Per.Fl l) l).symm e).untilt l := by
  have hp : ((frobeniusEquiv (Per.Fl l) l).symm e).untilt ^ l = 1 := by
    rw [← map_pow, frobeniusEquiv_symm_pow_p, h.1]
  have ho := orderOf_eq_prime hp h.2
  have := IsPrimitiveRoot.orderOf ((frobeniusEquiv (Per.Fl l) l).symm e).untilt
  rwa [ho] at this

/- English proof (translation)
Take `⟨⟨pf, hpf⟩, -, -, hX, -⟩` from `ReciprocityTheory.PGsh.a0 l ℂ_[l] Valued.v (Per.OC l) (PadicComplexInt.integers l)`. Conclude with `((hX e (PadicComplexInt.integers l) h.isPrimitiveRoot_untilt).2.2.2 pf hpf).1`.
-/
theorem ker_theta_eq_span_xi {l : ℕ} [Fact l.Prime] {e : Per.Fl l} (h : IsEps e) :
    RingHom.ker (Per.θ l) = Ideal.span {xi e} := by
  obtain ⟨⟨pf, hpf⟩, -, -, hX, -⟩ :=
    ReciprocityTheory.PGsh.a0 l ℂ_[l] Valued.v (Per.OC l) (PadicComplexInt.integers l)
  exact ((hX e (PadicComplexInt.integers l) h.isPrimitiveRoot_untilt).2.2.2 pf hpf).1

/- English proof (translation)
Introduce `e h a`. Rewrite using `[← RingHom.mem_ker, ker_theta_eq_span_xi h, Ideal.mem_span_singleton]`.
-/
theorem theta_eq_zero_iff_xi_dvd (l : ℕ) [Fact l.Prime] :
    ∀ e : Per.Fl l, IsEps e → ∀ a : Per.Ainf l, Per.θ l a = 0 ↔ xi e ∣ a := by
  intro e h a
  rw [← RingHom.mem_ker, ker_theta_eq_span_xi h, Ideal.mem_span_singleton]

end GlobalTheory.MemLoc
