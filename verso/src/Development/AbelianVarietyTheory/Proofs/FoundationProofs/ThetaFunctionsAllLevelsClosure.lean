import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLatticesFormSelfDualTriples

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaLevels

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_nsmul, bc_zero_left, pow_zero]`. Consider the case `succ n ih => rw [succ_nsmul, bc_add_left, ih, pow_succ]`.
-/
theorem bc_nsmul_left (D : D7) (T : Tor D) {N N' : ℕ} (n : ℕ) (x y : VC D N N') :
    bc D T (n • x) y = bc D T x y ^ n := by
  induction n with
  | zero => rw [zero_nsmul, bc_zero_left, pow_zero]
  | succ n ih => rw [succ_nsmul, bc_add_left, ih, pow_succ]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_nsmul, bc_zero_right, pow_zero]`. Consider the case `succ n ih => rw [succ_nsmul, bc_add_right, ih, pow_succ]`.
-/
theorem bc_nsmul_right (D : D7) (T : Tor D) {N N' : ℕ} (n : ℕ) (x y : VC D N N') :
    bc D T x (n • y) = bc D T x y ^ n := by
  induction n with
  | zero => rw [zero_nsmul, bc_zero_right, pow_zero]
  | succ n ih => rw [succ_nsmul, bc_add_right, ih, pow_succ]

/- English proof (translation)
Unfold `Wd U Hf`. Use `fun_prop`.
-/
theorem wd_entire (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (Wd D T x G) := by
  unfold Wd U Hf
  fun_prop

/- English proof (translation)
Introduce `D cc δ hc N N'`. Establish `hSD : ∀ n, SD D (stdL D n)` using `fun n => by`. Take `⟨Lt, h1, h2, -⟩` from `exists_lattice_of_adelic_point D n`. Rewrite using `[← h2]`. Conclude with `(h1 _).2`.

Establish `k : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N')` using `Or.inr ⟨_, _, hSD N, hSD N', rfl⟩`. Establish `n0` using `GlobalTheory.ThetaTriple.nice_of_klat hc k`. Use `⟨fun L L' hL hL' F hF => ?_, fun z F hF => ?_, fun F hF G hG => ?_, fun a F hF => ?_⟩` and prove the remaining obligations. Establish `k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L')` using `Or.inr ⟨_, _, hL, hL', rfl⟩`. Establish `n1` using `GlobalTheory.ThetaTriple.nice_of_klat hc k1`.

Take `⟨hd, hF⟩` from `(n1.mem_ThSp F).1 hF`. Use `⟨hd, _, Nat.pos_of_ne_zero (GlobalTheory.ThetaTriple.index_ne_zero hc k1 k), fun x hx => hF _ ?_⟩` and prove the remaining obligations. Conclude with `AddSubgroup.nsmul_index_mem ((La D (tor0 D cc δ) L L').addSubgroupOf (La0 D (tor0 D cc δ) N N')) ⟨x, hx⟩`. Take `⟨hd, m, hm, hF⟩` from `hF`. Take `⟨n, hn, hz⟩` from `GlobalTheory.ThetaInter.klat_mul_mem (GlobalTheory.InducedType.induced_type D).1.1 hc.1.1 k z`.

Express the relevant statement in the definitionally equal form `n • pt D (tor0 D cc δ) δ z ∈ _ at hz`. Use `⟨wd_entire D _ _ hd, m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hmx` using `AddSubgroup.nsmul_mem _ hx m`. Establish `h1 : bc D (tor0 D cc δ) ((m * n) • x) (pt D (tor0 D cc δ) δ z) = 1`. Rewrite using `[mul_comm, mul_smul, bc_nsmul_left, ← bc_nsmul_right]`.

Conclude with `n0.2.1 _ hmx _ hz`. Establish `h2 : bc D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) ((m * n) • x) = 1`. Rewrite using `[mul_comm, mul_smul, bc_nsmul_right, ← bc_nsmul_left]`. Conclude with `n0.2.1 _ hz _ hmx`. Establish `h3 : Wd D (tor0 D cc δ) ((m * n) • x) F = F`.

Rewrite using `[mul_smul]`. Conclude with `hF _ (AddSubgroup.nsmul_mem _ hx n)`. Establish `h4` using `Wd_Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) ((m * n) • x) F`. Rewrite `h4` using `[h3, h2, add_comm]`. Rewrite using `[Wd_Wd, h1, h4]`.

Take `⟨hd, m, hm, hF⟩` from `hF`. Take `⟨hd', n, hn, hG⟩` from `hG`. Use `⟨hd.add hd', m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1 : Wd D (tor0 D cc δ) ((m * n) • x) F = F`. Rewrite using `[mul_smul]`.

Conclude with `hF _ (AddSubgroup.nsmul_mem _ hx n)`. Establish `h2 : Wd D (tor0 D cc δ) ((m * n) • x) G = G`. Rewrite using `[mul_comm, mul_smul]`. Conclude with `hG _ (AddSubgroup.nsmul_mem _ hx m)`. Rewrite using `[Wd_add, h1, h2]`.

Take `⟨hd, m, hm, hF⟩` from `hF`. Conclude with `⟨hd.const_smul a, m, hm, fun x hx => by rw [Wd_smul, hF x hx]⟩`.
-/
theorem levels_closed : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ (L : Lat D N) (L' : Lat D N'), SD D L → SD D L' → ∀ F ∈ Th D (tor0 D cc δ) L L', F ∈ TT D (tor0 D cc δ) N N') ∧ (∀ (z : Matrix (Fin N') (Fin N) D.host.E), ∀ F ∈ TT D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F ∈ TT D (tor0 D cc δ) N N') ∧ (∀ F ∈ TT D (tor0 D cc δ) N N', ∀ G ∈ TT D (tor0 D cc δ) N N', F + G ∈ TT D (tor0 D cc δ) N N') ∧ ∀ (a : ℂ), ∀ F ∈ TT D (tor0 D cc δ) N N', a • F ∈ TT D (tor0 D cc δ) N N' := by
  intro D cc δ hc N N'
  have hSD : ∀ n, SD D (stdL D n) := fun n => by
    obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D n
    rw [← h2]; exact (h1 _).2
  have k : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, hSD N, hSD N', rfl⟩
  have n0 := GlobalTheory.ThetaTriple.nice_of_klat hc k
  refine ⟨fun L L' hL hL' F hF => ?_, fun z F hF => ?_, fun F hF G hG => ?_, fun a F hF => ?_⟩
  · have k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, hL, hL', rfl⟩
    have n1 := GlobalTheory.ThetaTriple.nice_of_klat hc k1
    obtain ⟨hd, hF⟩ := (n1.mem_ThSp F).1 hF
    refine ⟨hd, _, Nat.pos_of_ne_zero (GlobalTheory.ThetaTriple.index_ne_zero hc k1 k), fun x hx => hF _ ?_⟩
    exact AddSubgroup.nsmul_index_mem
      ((La D (tor0 D cc δ) L L').addSubgroupOf (La0 D (tor0 D cc δ) N N')) ⟨x, hx⟩
  · obtain ⟨hd, m, hm, hF⟩ := hF
    obtain ⟨n, hn, hz⟩ := GlobalTheory.ThetaInter.klat_mul_mem (GlobalTheory.InducedType.induced_type D).1.1 hc.1.1 k z
    change n • pt D (tor0 D cc δ) δ z ∈ _ at hz
    refine ⟨wd_entire D _ _ hd, m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
    have hmx := AddSubgroup.nsmul_mem _ hx m
    have h1 : bc D (tor0 D cc δ) ((m * n) • x) (pt D (tor0 D cc δ) δ z) = 1 := by
      rw [mul_comm, mul_smul, bc_nsmul_left, ← bc_nsmul_right]
      exact n0.2.1 _ hmx _ hz
    have h2 : bc D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) ((m * n) • x) = 1 := by
      rw [mul_comm, mul_smul, bc_nsmul_right, ← bc_nsmul_left]
      exact n0.2.1 _ hz _ hmx
    have h3 : Wd D (tor0 D cc δ) ((m * n) • x) F = F := by
      rw [mul_smul]; exact hF _ (AddSubgroup.nsmul_mem _ hx n)
    have h4 := Wd_Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) ((m * n) • x) F
    rw [h3, h2, add_comm] at h4
    rw [Wd_Wd, h1, h4]
  · obtain ⟨hd, m, hm, hF⟩ := hF
    obtain ⟨hd', n, hn, hG⟩ := hG
    refine ⟨hd.add hd', m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
    have h1 : Wd D (tor0 D cc δ) ((m * n) • x) F = F := by
      rw [mul_smul]; exact hF _ (AddSubgroup.nsmul_mem _ hx n)
    have h2 : Wd D (tor0 D cc δ) ((m * n) • x) G = G := by
      rw [mul_comm, mul_smul]; exact hG _ (AddSubgroup.nsmul_mem _ hx m)
    rw [Wd_add, h1, h2]
  · obtain ⟨hd, m, hm, hF⟩ := hF
    exact ⟨hd.const_smul a, m, hm, fun x hx => by rw [Wd_smul, hF x hx]⟩

end GlobalTheory.ThetaLevels
