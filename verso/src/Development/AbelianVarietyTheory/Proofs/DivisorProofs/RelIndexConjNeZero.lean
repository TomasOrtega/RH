import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section

namespace GlobalTheory.SphLineComm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨b, hb, hbv, x, hx, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨a * b, ?_, fun w => ?_, x, hx, by rw [mul_smul]⟩` and prove the remaining obligations. Establish `e : evI F (a * b) = evI F a * evI F b` using `map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1`.

Rewrite using `[e, ha, zero_mul]`. Rewrite using `[map_mul]`. Conclude with `mul_mem (hv w) (hbv w)`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem smul_mem_latHat {d : ℕ} (W : Spc F E d) (a : AF F) (ha : evI F a = 0)
    (hv : ∀ w : Pl F, evFin F w a ∈ w.adicCompletionIntegers F) {z : Fin d → AE F E} (hz : z ∈ latHat W) :
    a • z ∈ latHat W := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, hbv, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * b, ?_, fun w => ?_, x, hx, by rw [mul_smul]⟩
    · have e : evI F (a * b) = evI F a * evI F b := map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
      rw [e, ha, zero_mul]
    · rw [map_mul]
      exact mul_mem (hv w) (hbv w)
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.SphLineComm

end

namespace GlobalTheory.SphLineComm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

noncomputable def unitAt (v : Pl F) : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v 1)

/- English proof (translation)
Use `show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (singleFin v 1) = 1`. Conclude with `evalV_singleFin_self v 1`.
-/
theorem evFin_unitAt_self (v : Pl F) : evFin F v (unitAt v) = 1 := by
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (singleFin v 1) = 1
  exact evalV_singleFin_self v 1

/- English proof (translation)
Use `show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleFin v 1) = 0`. Conclude with `evalV_singleFin_ne h 1`.
-/
theorem evFin_unitAt_ne {v w : Pl F} (h : w ≠ v) : evFin F w (unitAt v) = 0 := by
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleFin v 1) = 0
  exact evalV_singleFin_ne h 1

/- English proof (translation)
Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0`. Conclude with `map_zero _`.
-/
theorem evI_unitAt (v : Pl F) : evI F (unitAt v) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
  exact map_zero _

end GlobalTheory.SphLineComm

namespace GlobalTheory.SphLineComm

/- English proof (translation)
Establish `hρ : ∀ a b z, ρ (a * b) z = ρ a (ρ b z)` using `fun a b z => by rw [map_mul]; rfl`. Establish `hρ1 : ∀ z, ρ 1 z = z` using `fun z => by rw [map_one]; rfl`. Establish `hKL : ∀ k ∈ K, ∀ z ∈ L, ρ k z ∈ L` using `fun k hk z hz => ((hK k).1 hk z hz).1`. Establish `hKL' : ∀ k ∈ K, ∀ z ∈ L, ρ k⁻¹ z ∈ L` using `fun k hk z hz => ((hK k).1 hk z hz).2`. Establish `step : ∀ h : G, (∀ z ∈ L, ∃ y ∈ L, ρ h z - z = (n * n) • y) → ∀ z ∈ L, ρ (g⁻¹ * h * g) z ∈ L`.

Introduce `h hc z hz`. Take `⟨y, hy, e⟩` from `hc (n • ρ g z) (hg z hz).1`. Establish `e2 : ρ h (ρ g z) - ρ g z = n • y`. Apply `sub_eq_zero.mp` to reduce the goal to its premises. Apply `htf` to reduce the goal to its premises.

Rewrite using `[smul_sub, smul_sub, ← map_nsmul, e, mul_smul, sub_self]`. Establish `e3 : ρ h (ρ g z) = ρ g z + n • y` using `by rw [← e2]; abel`. Establish `e4 : ρ g⁻¹ (ρ g z) = z` using `by rw [← hρ, inv_mul_cancel, hρ1]`. Rewrite using `[hρ, hρ, e3, map_add, map_nsmul, e4]`. Conclude with `L.add_mem hz (hg y hy).2`.

Establish `hcong : ∀ h ∈ K, (∀ z ∈ L, ∃ y ∈ L, ρ h z - z = (n * n) • y) → g⁻¹ * h * g ∈ K`. Introduce `h hh hc`. Establish `hc' : ∀ z ∈ L, ∃ y ∈ L, ρ h⁻¹ z - z = (n * n) • y`. Introduce `z hz`. Take `⟨y, hy, e⟩` from `hc (ρ h⁻¹ z) (hKL' h hh z hz)`.

Use `⟨-y, L.neg_mem hy, ?_⟩` and prove the remaining obligations. Establish `e' : ρ h (ρ h⁻¹ z) = z` using `by rw [← hρ, mul_inv_cancel, hρ1]`. Rewrite `e` using `[e']`. Rewrite using `[smul_neg, ← e]`. Normalize the expressions using the abelian group laws.

Use `(hK _).2 fun z hz => ⟨step h hc z hz, ?_⟩` and prove the remaining obligations. Establish `: (g⁻¹ * h * g)⁻¹ = g⁻¹ * h⁻¹ * g` using `by group`. Rewrite using `[this]`. Conclude with `step h⁻¹ hc' z hz`. Establish `hsel : ∀ (k : K) (s : S), ∃ s' : S, ∃ y ∈ L, π (ρ k s) - s' = (n * n) • y`.

Introduce `k s`. Take `⟨s', hs', y, hy, e⟩` from `hfin (ρ k s) (hKL k k.2 s (hS s s.2))`. Conclude with `⟨⟨s', hs'⟩, y, hy, e⟩`. Use `choose f hf using hsel`. Establish `key : ∀ k1 k2 : K, f k1 = f k2 → ∀ z ∈ L, ∃ y ∈ L, ρ ((k1 : G)⁻¹ * k2) z - z = (n * n) • y`.

Introduce `k1 k2 h12 z hz`. Establish `hd : ∀ s : S, ∃ y ∈ L, ρ k2 s - ρ k1 s = (n * n) • y`. Introduce `s`. Take `⟨y1, hy1, e1⟩` from `hf k1 s`. Take `⟨y2, hy2, e2⟩` from `hf k2 s`.

Use `⟨y2 - y1, L.sub_mem hy2 hy1, ?_⟩` and prove the remaining obligations. Establish `a1 : ρ k1 s - s = π (ρ k1 s) - π s` using `by rw [hπ, hπ']`. Establish `a2 : ρ k2 s - s = π (ρ k2 s) - π s` using `by rw [hπ, hπ']`. Rewrite `e1` using `[congrFun h12 s]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨s, hs, y, hy, e⟩` from `hfin z hz`. Take `⟨y', hy', e'⟩` from `hd ⟨s, hs⟩`. Establish `hz' : π z = s + (n * n) • y` using `by rw [← e]; abel`. Establish `hdiff : ρ k2 z - ρ k1 z = (n * n) • (y' + (ρ k2 y - ρ k1 y))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hz', map_add, map_add, map_nsmul, map_nsmul, smul_add, smul_sub]`. Simplify using `only at e'`. Rewrite using `[← e']`. Normalize the expressions using the abelian group laws. Use `⟨ρ (k1 : G)⁻¹ (y' + (ρ k2 y - ρ k1 y)), hKL' _ k1.2 _ (L.add_mem hy' (L.sub_mem (hKL _ k2.2 y hy) (hKL _ k1.2 y hy))), ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_nsmul, ← hdiff, map_sub, hρ, ← hρ (k1 : G)⁻¹ k1 z, inv_mul_cancel, hρ1]`. Use `haveI : Finite (K ⧸ (K.map (MulAut.conj g).toMonoidHom).subgroupOf K) := by`. Use `Finite.of_injective (fun q : K ⧸ (K.map (MulAut.conj g).toMonoidHom).subgroupOf K => f q.out) ?_` and prove the remaining obligations. Introduce `q1 q2 hq`. Rewrite using `[← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, QuotientGroup.eq, Subgroup.mem_subgroupOf]`.

Establish `hmem : ((q1.out : G))⁻¹ * q2.out ∈ K` using `K.mul_mem (K.inv_mem q1.out.2) q2.out.2`. Establish `h2` using `hcong _ hmem (key _ _ hq)`. Use `⟨_, h2, ?_⟩` and prove the remaining obligations. Simplify using `[MulAut.conj_apply, mul_assoc]`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_conj_ne_zero {G V : Type} [Group G] [AddCommGroup V] (ρ : G →* AddMonoid.End V)
    (L : AddSubgroup V) (K : Subgroup G) (hK : ∀ k, k ∈ K ↔ ∀ z ∈ L, ρ k z ∈ L ∧ ρ k⁻¹ z ∈ L)
    (π : V →+ V) (hπ : ∀ k z, ρ k z - z = ρ k (π z) - π z) (hπ' : ∀ k z, ρ k (π z) = π (ρ k z))
    (g : G) (n : ℕ) (htf : ∀ x : V, n • x = 0 → x = 0) (hg : ∀ z ∈ L, n • ρ g z ∈ L ∧ n • ρ g⁻¹ z ∈ L)
    (S : Finset V) (hS : ∀ s ∈ S, s ∈ L) (hfin : ∀ z ∈ L, ∃ s ∈ S, ∃ y ∈ L, π z - s = (n * n) • y) :
    (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0 := by
  classical
  have hρ : ∀ a b z, ρ (a * b) z = ρ a (ρ b z) := fun a b z => by rw [map_mul]; rfl
  have hρ1 : ∀ z, ρ 1 z = z := fun z => by rw [map_one]; rfl
  have hKL : ∀ k ∈ K, ∀ z ∈ L, ρ k z ∈ L := fun k hk z hz => ((hK k).1 hk z hz).1
  have hKL' : ∀ k ∈ K, ∀ z ∈ L, ρ k⁻¹ z ∈ L := fun k hk z hz => ((hK k).1 hk z hz).2
  have step : ∀ h : G, (∀ z ∈ L, ∃ y ∈ L, ρ h z - z = (n * n) • y) → ∀ z ∈ L, ρ (g⁻¹ * h * g) z ∈ L := by
    intro h hc z hz
    obtain ⟨y, hy, e⟩ := hc (n • ρ g z) (hg z hz).1
    have e2 : ρ h (ρ g z) - ρ g z = n • y := by
      apply sub_eq_zero.mp
      apply htf
      rw [smul_sub, smul_sub, ← map_nsmul, e, mul_smul, sub_self]
    have e3 : ρ h (ρ g z) = ρ g z + n • y := by rw [← e2]; abel
    have e4 : ρ g⁻¹ (ρ g z) = z := by rw [← hρ, inv_mul_cancel, hρ1]
    rw [hρ, hρ, e3, map_add, map_nsmul, e4]
    exact L.add_mem hz (hg y hy).2
  have hcong : ∀ h ∈ K, (∀ z ∈ L, ∃ y ∈ L, ρ h z - z = (n * n) • y) → g⁻¹ * h * g ∈ K := by
    intro h hh hc
    have hc' : ∀ z ∈ L, ∃ y ∈ L, ρ h⁻¹ z - z = (n * n) • y := by
      intro z hz
      obtain ⟨y, hy, e⟩ := hc (ρ h⁻¹ z) (hKL' h hh z hz)
      refine ⟨-y, L.neg_mem hy, ?_⟩
      have e' : ρ h (ρ h⁻¹ z) = z := by rw [← hρ, mul_inv_cancel, hρ1]
      rw [e'] at e
      rw [smul_neg, ← e]; abel
    refine (hK _).2 fun z hz => ⟨step h hc z hz, ?_⟩
    have : (g⁻¹ * h * g)⁻¹ = g⁻¹ * h⁻¹ * g := by group
    rw [this]
    exact step h⁻¹ hc' z hz
  have hsel : ∀ (k : K) (s : S), ∃ s' : S, ∃ y ∈ L, π (ρ k s) - s' = (n * n) • y := by
    intro k s
    obtain ⟨s', hs', y, hy, e⟩ := hfin (ρ k s) (hKL k k.2 s (hS s s.2))
    exact ⟨⟨s', hs'⟩, y, hy, e⟩
  choose f hf using hsel
  have key : ∀ k1 k2 : K, f k1 = f k2 → ∀ z ∈ L, ∃ y ∈ L, ρ ((k1 : G)⁻¹ * k2) z - z = (n * n) • y := by
    intro k1 k2 h12 z hz
    have hd : ∀ s : S, ∃ y ∈ L, ρ k2 s - ρ k1 s = (n * n) • y := by
      intro s
      obtain ⟨y1, hy1, e1⟩ := hf k1 s
      obtain ⟨y2, hy2, e2⟩ := hf k2 s
      refine ⟨y2 - y1, L.sub_mem hy2 hy1, ?_⟩
      have a1 : ρ k1 s - s = π (ρ k1 s) - π s := by rw [hπ, hπ']
      have a2 : ρ k2 s - s = π (ρ k2 s) - π s := by rw [hπ, hπ']
      rw [congrFun h12 s] at e1
      calc ρ k2 s - ρ k1 s = (ρ k2 s - s) - (ρ k1 s - s) := by abel
        _ = (π (ρ k2 (s : V)) - (f k2 s : V)) - (π (ρ k1 (s : V)) - (f k2 s : V)) := by rw [a1, a2]; abel
        _ = _ := by rw [e1, e2, smul_sub]
    obtain ⟨s, hs, y, hy, e⟩ := hfin z hz
    obtain ⟨y', hy', e'⟩ := hd ⟨s, hs⟩
    have hz' : π z = s + (n * n) • y := by rw [← e]; abel
    have hdiff : ρ k2 z - ρ k1 z = (n * n) • (y' + (ρ k2 y - ρ k1 y)) := by
      calc ρ k2 z - ρ k1 z = (ρ k2 z - z) - (ρ k1 z - z) := by abel
        _ = ρ k2 (π z) - ρ k1 (π z) := by rw [hπ k2 z, hπ k1 z]; abel
        _ = _ := by
          rw [hz', map_add, map_add, map_nsmul, map_nsmul, smul_add, smul_sub]
          simp only at e'
          rw [← e']; abel
    refine ⟨ρ (k1 : G)⁻¹ (y' + (ρ k2 y - ρ k1 y)),
      hKL' _ k1.2 _ (L.add_mem hy' (L.sub_mem (hKL _ k2.2 y hy) (hKL _ k1.2 y hy))), ?_⟩
    rw [← map_nsmul, ← hdiff, map_sub, hρ, ← hρ (k1 : G)⁻¹ k1 z, inv_mul_cancel, hρ1]
  haveI : Finite (K ⧸ (K.map (MulAut.conj g).toMonoidHom).subgroupOf K) := by
    refine Finite.of_injective (fun q : K ⧸ (K.map (MulAut.conj g).toMonoidHom).subgroupOf K => f q.out) ?_
    intro q1 q2 hq
    rw [← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hmem : ((q1.out : G))⁻¹ * q2.out ∈ K := K.mul_mem (K.inv_mem q1.out.2) q2.out.2
    have h2 := hcong _ hmem (key _ _ hq)
    refine ⟨_, h2, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.SphLineComm
