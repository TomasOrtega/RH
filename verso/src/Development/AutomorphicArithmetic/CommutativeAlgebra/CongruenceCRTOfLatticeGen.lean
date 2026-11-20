import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVectorEqNsmulOfAdelicNsmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromPStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.VqInduction

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

namespace UpperTheory.Gal.Int.Geo.CRT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

/- English proof (translation)
Introduce `v` and use `by rw [map_one]; exact one_mem _`.
-/
private theorem isInt_one' : IsIntAf (1 : AfP p) := fun v => by
  rw [map_one]; exact one_mem _

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨1, x, isInt_one', rfl⟩`.
-/
private theorem inAf_mem' (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, isInt_one', rfl⟩

/- English proof (translation)
Simplify using `[mulF, actQ]`. Both sides reduce to the same expression.
-/
private theorem mulF_tmul (c : 𝓞 D.F) (a : AfP p) (t : ℚ) (x : D.La) :
    mulF D c (a ⊗ₜ (t ⊗ₜ x)) = a ⊗ₜ (t ⊗ₜ (algebraMap (𝓞 D.F) D.O c • x)) := by
  simp [mulF, actQ]
  rfl

/- English proof (translation)
The claim follows from `mulF_tmul c 1 1 x`.
-/
private theorem mulF_inAf (c : 𝓞 D.F) (x : D.La) :
    mulF D c (inAf D x) = inAf D (algebraMap (𝓞 D.F) D.O c • x) := mulF_tmul c 1 1 x

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qk61.vq_induction h0 hadd ht v`.
-/
private theorem vq_induction {P : AfP p ⊗[ℚ] VQ D → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (ht : ∀ (a : AfP p) (t : ℚ) (x : D.La), P (a ⊗ₜ (t ⊗ₜ x))) (v : AfP p ⊗[ℚ] VQ D) : P v :=
  _root_.UpperTheory.Reformulated.B.Qk61.vq_induction h0 hadd ht v

/- English proof (translation)
Use `vq_induction (P := fun v => mulF D (c * d) v = mulF D c (mulF D d v)) (by simp) ?_ ?_ v` and prove the remaining obligations. Introduce `x y hx hy`. Simplify using `only [map_add, hx, hy]`. Introduce `a t x`. Simplify using `only [mulF_tmul, map_mul, mul_smul]`.
-/
private theorem mulF_mul (c d : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) : mulF D (c * d) v = mulF D c (mulF D d v) := by
  refine vq_induction (P := fun v => mulF D (c * d) v = mulF D c (mulF D d v)) (by simp) ?_ ?_ v
  · intro x y hx hy; simp only [map_add, hx, hy]
  · intro a t x; simp only [mulF_tmul, map_mul, mul_smul]

/- English proof (translation)
Use `vq_induction (P := fun v => mulF D (c + d) v = mulF D c v + mulF D d v) (by simp) ?_ ?_ v` and prove the remaining obligations. Introduce `x y hx hy`. Simplify using `only [map_add, hx, hy]`. Normalize the expressions using the abelian group laws. Introduce `a t x`.

Simplify using `only [mulF_tmul, map_add, add_smul, TensorProduct.tmul_add]`.
-/
private theorem mulF_add (c d : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) : mulF D (c + d) v = mulF D c v + mulF D d v := by
  refine vq_induction (P := fun v => mulF D (c + d) v = mulF D c v + mulF D d v) (by simp) ?_ ?_ v
  · intro x y hx hy; simp only [map_add, hx, hy]; abel
  · intro a t x; simp only [mulF_tmul, map_add, add_smul, TensorProduct.tmul_add]

/- English proof (translation)
Use `vq_induction (P := fun v => mulF D 1 v = v) (by simp) ?_ ?_ v` and prove the remaining obligations. Introduce `x y hx hy`. Simplify using `only [map_add, hx, hy]`. Introduce `a t x`. Simplify using `only [mulF_tmul, map_one, one_smul]`.
-/
private theorem mulF_one (v : AfP p ⊗[ℚ] VQ D) : mulF D 1 v = v := by
  refine vq_induction (P := fun v => mulF D 1 v = v) (by simp) ?_ ?_ v
  · intro x y hx hy; simp only [map_add, hx, hy]
  · intro a t x; simp only [mulF_tmul, map_one, one_smul]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Use `vq_induction (P := fun v => mulF D ((0 : ℕ) : 𝓞 D.F) v = (0 : ℕ) • v) (by simp) ?_ ?_ v` and prove the remaining obligations. Introduce `x y hx hy`. Simplify using `only [map_add, hx, hy]`.

Simplify using the standard rewrite rules. Introduce `a t x`. Simplify using `[mulF_tmul]`. Consider the case `succ n ih => rw [Nat.cast_succ, mulF_add, mulF_one, ih, succ_nsmul]`.
-/
private theorem mulF_nat (n : ℕ) (v : AfP p ⊗[ℚ] VQ D) : mulF D (n : 𝓞 D.F) v = n • v := by
  induction n with
  | zero =>
    refine vq_induction (P := fun v => mulF D ((0 : ℕ) : 𝓞 D.F) v = (0 : ℕ) • v) (by simp) ?_ ?_ v
    · intro x y hx hy; simp only [map_add, hx, hy]; simp
    · intro a t x; simp [mulF_tmul]
  | succ n ih => rw [Nat.cast_succ, mulF_add, mulF_one, ih, succ_nsmul]

/- English proof (translation)
Proceed by induction on `hv using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, x, ha, rfl⟩` from `hz`. Rewrite using `[mulF_tmul]`. Conclude with `AddSubgroup.subset_closure ⟨a, _, ha, rfl⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg]`.

Conclude with `neg_mem hx`.
-/
private theorem mulF_mem (c : 𝓞 D.F) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : mulF D c v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    rw [mulF_tmul]
    exact AddSubgroup.subset_closure ⟨a, _, ha, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨x, hx, v, hv, rfl⟩`.
-/
private theorem mem_idHat {𝔟 : Ideal (𝓞 D.F)} {x : 𝓞 D.F} (hx : x ∈ 𝔟) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    mulF D x v ∈ idHat D 𝔟 := AddSubgroup.subset_closure ⟨x, hx, v, hv, rfl⟩

/- English proof (translation)
The claim follows from `(AddSubgroup.closure_le _).2 (by rintro _ ⟨x, hx, v, hv, rfl⟩; exact h x hx v hv)`.
-/
private theorem idHat_ind {𝔟 : Ideal (𝓞 D.F)} {S : AddSubgroup (AfP p ⊗[ℚ] VQ D)}
    (h : ∀ x ∈ 𝔟, ∀ v ∈ LaHat D, mulF D x v ∈ S) : idHat D 𝔟 ≤ S :=
  (AddSubgroup.closure_le _).2 (by rintro _ ⟨x, hx, v, hv, rfl⟩; exact h x hx v hv)

/- English proof (translation)
The claim follows from `idHat_ind fun _ hx _ hv => mem_idHat (h hx) hv`.
-/
private theorem idHat_mono {𝔟 𝔠 : Ideal (𝓞 D.F)} (h : 𝔟 ≤ 𝔠) : idHat D 𝔟 ≤ idHat D 𝔠 :=
  idHat_ind fun _ hx _ hv => mem_idHat (h hx) hv

/- English proof (translation)
Establish `: idHat D 𝔟 ≤ (idHat D (𝔠 * 𝔟)).comap (mulF D c).toAddMonoidHom` using `idHat_ind fun x hx w hw => by`. Express the relevant statement in the definitionally equal form `mulF D c (mulF D x w) ∈ idHat D (𝔠 * 𝔟)`. Rewrite using `[← mulF_mul]`. Conclude with `mem_idHat (Ideal.mul_mem_mul hc hx) hw`. Conclude with `this hv`.
-/
private theorem mulF_mem_idHat_mul {𝔟 𝔠 : Ideal (𝓞 D.F)} {c : 𝓞 D.F} (hc : c ∈ 𝔠) {v : AfP p ⊗[ℚ] VQ D}
    (hv : v ∈ idHat D 𝔟) : mulF D c v ∈ idHat D (𝔠 * 𝔟) := by
  have : idHat D 𝔟 ≤ (idHat D (𝔠 * 𝔟)).comap (mulF D c).toAddMonoidHom := idHat_ind fun x hx w hw => by
    change mulF D c (mulF D x w) ∈ idHat D (𝔠 * 𝔟)
    rw [← mulF_mul]
    exact mem_idHat (Ideal.mul_mem_mul hc hx) hw
  exact this hv

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, add_mul, mul_add, hx, hy]`. Consider the case `tmul r c`. Establish `e : actOn L.rep (AfP p) (r ⊗ₜ c) = r • (L.rep c).baseChange (AfP p)`.

Establish `e0 : actOn L.rep (AfP p) (r ⊗ₜ c) = (Algebra.ofId (AfP p) (Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) r) * (Module.End.baseChangeHom ℚ (AfP p) (VQ D)) (L.rep c)` using `Algebra.TensorProduct.lift_tmul _ _ _ _ _`. Rewrite using `[e0, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, _root_.one_mul]`. Both sides reduce to the same expression. Establish `h` using `(L.rep_range (L.rep c)).1 ⟨c, rfl⟩ b`. Establish `h2 : (L.rep c).baseChange (AfP p) * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * (L.rep c).baseChange (AfP p)`.

Use `congrArg (Module.End.baseChangeHom ℚ (AfP p) (VQ D)) h` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul]`. Conclude with `this`. Rewrite using `[e, smul_mul_assoc, mul_smul_comm, h2]`.
-/
private theorem actOn_comm (L : Link D G) (y : AfP p ⊗[ℚ] G.C) (b : D.O) :
    actOn L.rep (AfP p) y * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * actOn L.rep (AfP p) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, add_mul, mul_add, hx, hy]
  | tmul r c =>
    have e : actOn L.rep (AfP p) (r ⊗ₜ c) = r • (L.rep c).baseChange (AfP p) := by
      have e0 : actOn L.rep (AfP p) (r ⊗ₜ c) =
          (Algebra.ofId (AfP p) (Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) r) * (Module.End.baseChangeHom ℚ (AfP p) (VQ D)) (L.rep c) :=
        Algebra.TensorProduct.lift_tmul _ _ _ _ _
      rw [e0, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, _root_.one_mul]
      rfl
    have h := (L.rep_range (L.rep c)).1 ⟨c, rfl⟩ b
    have h2 : (L.rep c).baseChange (AfP p) * (actQ D b).baseChange (AfP p) =
        (actQ D b).baseChange (AfP p) * (L.rep c).baseChange (AfP p) := by
      have := congrArg (Module.End.baseChangeHom ℚ (AfP p) (VQ D)) h
      rw [map_mul, map_mul] at this
      exact this
    rw [e, smul_mul_assoc, mul_smul_comm, h2]

/- English proof (translation)
The claim follows from `LinearMap.congr_fun (actOn_comm L _ (algebraMap (𝓞 D.F) D.O c)) v`.
-/
private theorem actG_mulF (L : Link D G) (g : G.GAf) (c : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) :
    L.actG g (mulF D c v) = mulF D c (L.actG g v) :=
  LinearMap.congr_fun (actOn_comm L _ (algebraMap (𝓞 D.F) D.O c)) v

/- English proof (translation)
Establish `key : ∀ b : D.O, inAf D (b • y) ∈ idHat D 𝔞`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨c, hc, z', rfl⟩` from `hz`. Introduce `b`.

Rewrite `hc` using `[pow_one]`. Establish `e : b • algebraMap (𝓞 D.F) D.O c • z' = algebraMap (𝓞 D.F) D.O c • b • z'`. Rewrite using `[smul_smul, smul_smul, Algebra.commutes]`. Rewrite using `[e, ← mulF_inAf]`. Conclude with `mem_idHat hc (inAf_mem' _)`.

Consider the case `zero`. Introduce `b`. Rewrite using `[smul_zero]`. Establish `: inAf D (0 : D.La) = 0` using `by simp [inAf]`. Rewrite using `[this]`.

Conclude with `zero_mem _`. Consider the case `add x z _ _ hx hz`. Introduce `b`. Establish `: inAf D (b • (x + z)) = inAf D (b • x) + inAf D (b • z)`. Simplify using `[inAf, smul_add, TensorProduct.tmul_add]`.

Rewrite using `[this]`. Conclude with `add_mem (hx b) (hz b)`. Consider the case `smul c x _ hx`. Introduce `b`. Rewrite using `[smul_smul]`.

Conclude with `hx _`. Simplify using `using key 1`.
-/
private theorem wSub_inAf {𝔞 : Ideal (𝓞 D.F)} {y : D.La} (hy : y ∈ wSub D 𝔞 1) : inAf D y ∈ idHat D 𝔞 := by
  have key : ∀ b : D.O, inAf D (b • y) ∈ idHat D 𝔞 := by
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, hc, z', rfl⟩ := hz
      intro b
      rw [pow_one] at hc
      have e : b • algebraMap (𝓞 D.F) D.O c • z' = algebraMap (𝓞 D.F) D.O c • b • z' := by
        rw [smul_smul, smul_smul, Algebra.commutes]
      rw [e, ← mulF_inAf]
      exact mem_idHat hc (inAf_mem' _)
    | zero =>
      intro b
      rw [smul_zero]
      have : inAf D (0 : D.La) = 0 := by simp [inAf]
      rw [this]; exact zero_mem _
    | add x z _ _ hx hz =>
      intro b
      have : inAf D (b • (x + z)) = inAf D (b • x) + inAf D (b • z) := by
        simp [inAf, smul_add, TensorProduct.tmul_add]
      rw [this]; exact add_mem (hx b) (hz b)
    | smul c x _ hx =>
      intro b
      rw [smul_smul]; exact hx _
  simpa using key 1

/- English proof (translation)
Proceed by induction on `hv using AddSubgroup.closure_induction with`. Consider the case `mem u hu`. Take `⟨x, hx, w, hw, rfl⟩` from `hu`. Take `⟨z, hz⟩` from `h x hx`. Conclude with `⟨mulF D z w, mulF_mem z hw, by rw [← mulF_mul, hz, mulF_mul, mulF_nat]⟩`.

Consider the case `zero => exact ⟨0, zero_mem _, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨w, hw, ew⟩` from `hx`. Take `⟨w', hw', ew'⟩` from `hy`. Conclude with `⟨w + w', add_mem hw hw', by rw [map_add, ew, ew', smul_add]⟩`.

Consider the case `neg x _ hx`. Take `⟨w, hw, ew⟩` from `hx`. Conclude with `⟨-w, neg_mem hw, by rw [map_neg, ew, smul_neg]⟩`.
-/
private theorem div_of_idHat {𝔟 : Ideal (𝓞 D.F)} {c : 𝓞 D.F} {N : ℕ} (h : ∀ x ∈ 𝔟, ∃ z : 𝓞 D.F, c * x = N * z)
    {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ idHat D 𝔟) : ∃ w ∈ LaHat D, mulF D c v = N • w := by
  induction hv using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨x, hx, w, hw, rfl⟩ := hu
    obtain ⟨z, hz⟩ := h x hx
    exact ⟨mulF D z w, mulF_mem z hw, by rw [← mulF_mul, hz, mulF_mul, mulF_nat]⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, ew⟩ := hx
    obtain ⟨w', hw', ew'⟩ := hy
    exact ⟨w + w', add_mem hw hw', by rw [map_add, ew, ew', smul_add]⟩
  | neg x _ hx =>
    obtain ⟨w, hw, ew⟩ := hx
    exact ⟨-w, neg_mem hw, by rw [map_neg, ew, smul_neg]⟩

/- English proof (translation)
Establish `hN : (N₀ : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)}` using `Ideal.mem_span_singleton_self _`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun v hv => ?_, fun v hv => idHat_mono Ideal.mul_le_right (h v hv)⟩` and prove the remaining obligations. Take `⟨w, hw, ew⟩` from `div_of_idHat (c := 1) (N := N₀) (fun x hx => by`.

Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.1 (Ideal.mul_le_left hx)`. Conclude with `⟨z, by rw [_root_.one_mul, ← hz, _root_.mul_comm]⟩) (h v hv)`. Rewrite `ew` using `[mulF_one]`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Rewrite using `[← ew]`.

Normalize the expressions using the abelian group laws. Introduce and unpack `⟨h1, h2⟩ v hv`. Take `⟨w, hw, ew⟩` from `h1 v hv`. Establish `hu : L.actG g v - v = N₀ • w` using `by rw [ew]; abel`. Establish `hu2` using `h2 v hv`.

Establish `dec : L.actG g v - v = mulF D ((N₀ : 𝓞 D.F) * s) (L.actG g v - v) + mulF D t (L.actG g v - v)`. Rewrite using `[← mulF_add, e, mulF_one]`. Rewrite using `[dec]`. Use `add_mem (mulF_mem_idHat_mul (Ideal.mul_mem_right _ _ hN) hu2) ?_` and prove the remaining obligations. Rewrite using `[hu, ← mulF_nat, ← mulF_mul, _root_.mul_comm t]`.

Conclude with `mem_idHat (Ideal.mul_mem_mul hN ht) hw`.
-/
private theorem crt_part (L : Link D G) (N₀ : ℕ) (𝔞 : Ideal (𝓞 D.F)) (s t : 𝓞 D.F) (ht : t ∈ 𝔞)
    (e : (N₀ : 𝓞 D.F) * s + t = 1) (g : G.GAf) :
    CongId L (Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞) g ↔ L.CongOne N₀ g ∧ CongId L 𝔞 g := by
  have hN : (N₀ : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} := Ideal.mem_span_singleton_self _
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun v hv => idHat_mono Ideal.mul_le_right (h v hv)⟩
    obtain ⟨w, hw, ew⟩ := div_of_idHat (c := 1) (N := N₀) (fun x hx => by
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Ideal.mul_le_left hx)
      exact ⟨z, by rw [_root_.one_mul, ← hz, _root_.mul_comm]⟩) (h v hv)
    rw [mulF_one] at ew
    refine ⟨w, hw, ?_⟩
    rw [← ew]; abel
  · rintro ⟨h1, h2⟩ v hv
    obtain ⟨w, hw, ew⟩ := h1 v hv
    have hu : L.actG g v - v = N₀ • w := by rw [ew]; abel
    have hu2 := h2 v hv
    have dec : L.actG g v - v = mulF D ((N₀ : 𝓞 D.F) * s) (L.actG g v - v) + mulF D t (L.actG g v - v) := by
      rw [← mulF_add, e, mulF_one]
    rw [dec]
    refine add_mem (mulF_mem_idHat_mul (Ideal.mul_mem_right _ _ hN) hu2) ?_
    rw [hu, ← mulF_nat, ← mulF_mul, _root_.mul_comm t]
    exact mem_idHat (Ideal.mul_mem_mul hN ht) hw

/- English proof (translation)
Establish `hq : ((q : 𝓞 D.F)) ^ e ∈ 𝔞` using `he (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_insert _ _)) e)`. Establish `hc' : IsCoprime (N₀ : ℤ) ((q ^ e : ℕ) : ℤ)` using `Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right e hc)`. Take `⟨u, v, huv⟩` from `hc'`. Use `⟨(u : 𝓞 D.F), (v : 𝓞 D.F) * (q : 𝓞 D.F) ^ e, Ideal.mul_mem_left _ _ hq, ?_⟩` and prove the remaining obligations. Use `congrArg (Int.cast : ℤ → 𝓞 D.F) huv` as an intermediate fact.

Move the coercions through the operations in `at this`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem bezout {q N₀ : ℕ} {r : ℤ} {𝔞 : Ideal (𝓞 D.F)} (hc : N₀.Coprime q) (e : ℕ) (he : uId D q r ^ e ≤ 𝔞) :
    ∃ s t : 𝓞 D.F, t ∈ 𝔞 ∧ (N₀ : 𝓞 D.F) * s + t = 1 := by
  have hq : ((q : 𝓞 D.F)) ^ e ∈ 𝔞 :=
    he (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_insert _ _)) e)
  have hc' : IsCoprime (N₀ : ℤ) ((q ^ e : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right e hc)
  obtain ⟨u, v, huv⟩ := hc'
  refine ⟨(u : 𝓞 D.F), (v : 𝓞 D.F) * (q : 𝓞 D.F) ^ e, Ideal.mul_mem_left _ _ hq, ?_⟩
  have := congrArg (Int.cast : ℤ → 𝓞 D.F) huv
  push_cast at this
  rw [← this]; ring

/- English proof (translation)
Establish `hNa : (N : 𝓞 D.F) ∈ 𝔞`. Establish `: (N : 𝓞 D.F) ∈ (Ideal.span {a} ⊔ Ideal.span {(N : 𝓞 D.F)}) * 𝔞`. Rewrite using `[show (Ideal.span {a} ⊔ Ideal.span {(N : 𝓞 D.F)}) * 𝔞 = _ from hgen]`. Conclude with `Ideal.mem_span_singleton_self _`. Conclude with `Ideal.mul_le_right this`.

Establish `hax : ∀ x ∈ 𝔞, ∃ z : 𝓞 D.F, a * x = N * z` using `fun x hx => by`. Establish `: a * x ∈ Ideal.span {(N : 𝓞 D.F)}`. Rewrite using `[← show (Ideal.span {a} ⊔ Ideal.span {(N : 𝓞 D.F)}) * 𝔞 = _ from hgen]`. Conclude with `Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) hx`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.1 this`.

Conclude with `⟨z, by rw [← hz, _root_.mul_comm]⟩`. Prove the components needed by the constructor for the conclusion. Introduce `h y`. Take `⟨w, hw, ew⟩` from `div_of_idHat hax (h _ (inAf_mem' y))`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations.

Rewrite `ew` using `[map_sub, ← actG_mulF, mulF_inAf]`. Rewrite using `[← ew]`. Normalize the expressions using the abelian group laws. Introduce `h`. Establish `step1 : ∀ v ∈ LaHat D, ∃ w ∈ LaHat D, mulF D a (L.actG g v - v) = N • w` using `fun v hv => by`.

Take `⟨x, w', hw', rfl⟩` from `GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D N hN hNp v hv`. Take `⟨v₁, hv₁, e₁⟩` from `h x`. Use `⟨v₁ + mulF D a (L.actG g w' - w'), add_mem hv₁ (mulF_mem a (sub_mem (hg _ hw') hw')), ?_⟩` and prove the remaining obligations. Establish `e₂ : mulF D a (L.actG g (inAf D x) - inAf D x) = N • v₁`. Rewrite using `[map_sub, ← actG_mulF, mulF_inAf, e₁]`.

Normalize the expressions using the abelian group laws. Establish `e₃ : L.actG g (inAf D x + N • w') - (inAf D x + N • w') = (L.actG g (inAf D x) - inAf D x) + N • (L.actG g w' - w')`. Rewrite using `[map_add, map_nsmul, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e₃, map_add, e₂, map_nsmul, smul_add]`.

Introduce `v hv`. Establish `hu : L.actG g v - v ∈ LaHat D` using `sub_mem (hg v hv) hv`. Take `⟨w₁, hw₁, e₁⟩` from `step1 v hv`. Take `⟨y, w, hw, e₂⟩` from `GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D N hN hNp _ hu`. Establish `hdvd : ∃ u : D.La, algebraMap (𝓞 D.F) D.O a • y = N • u`.

Use `GlobalTheory.T.exists_latticeVector_eq_nsmul_of_adelic_nsmul p D N hN hNp (GlobalTheory.T.int_dvd_of_eq_nat_mul_integralAdeleAwayFromP p N hN hNp) _ ⟨w₁ - mulF D a w, sub_mem hw₁ (mulF_mem a hw), ?_⟩` and prove the remaining obligations. Rewrite `e₁` using `[e₂, map_add, mulF_inAf, map_nsmul]`. Rewrite using `[smul_sub, ← e₁]`. Normalize the expressions using the abelian group laws. Establish `hy : y ∈ wSub D 𝔞 1` using `((hLG p D a N 𝔞 hN hgen).1 y).1 hdvd`.

Rewrite using `[e₂]`. Use `add_mem (wSub_inAf hy) ?_` and prove the remaining obligations. Rewrite using `[← mulF_nat]`. Conclude with `mem_idHat hNa hw`.
-/
private theorem gen_part (hLG : LatGen) (L : Link D G) (𝔞 : Ideal (𝓞 D.F)) (g : G.GAf) (hg : Integ L g)
    (a : 𝓞 D.F) (N : ℕ) (hN : 0 < N) (hNp : N.Coprime p) (hgen : IsGen a N 𝔞) :
    CongId L 𝔞 g ↔ ∀ y : D.La, ∃ v ∈ LaHat D,
      L.actG g (inAf D (algebraMap (𝓞 D.F) D.O a • y)) = inAf D (algebraMap (𝓞 D.F) D.O a • y) + N • v := by
  have hNa : (N : 𝓞 D.F) ∈ 𝔞 := by
    have : (N : 𝓞 D.F) ∈ (Ideal.span {a} ⊔ Ideal.span {(N : 𝓞 D.F)}) * 𝔞 := by
      rw [show (Ideal.span {a} ⊔ Ideal.span {(N : 𝓞 D.F)}) * 𝔞 = _ from hgen]
      exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_right this
  have hax : ∀ x ∈ 𝔞, ∃ z : 𝓞 D.F, a * x = N * z := fun x hx => by
    have : a * x ∈ Ideal.span {(N : 𝓞 D.F)} := by
      rw [← show (Ideal.span {a} ⊔ Ideal.span {(N : 𝓞 D.F)}) * 𝔞 = _ from hgen]
      exact Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) hx
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨z, by rw [← hz, _root_.mul_comm]⟩
  constructor
  · intro h y
    obtain ⟨w, hw, ew⟩ := div_of_idHat hax (h _ (inAf_mem' y))
    refine ⟨w, hw, ?_⟩
    rw [map_sub, ← actG_mulF, mulF_inAf] at ew
    rw [← ew]; abel
  · intro h
    have step1 : ∀ v ∈ LaHat D, ∃ w ∈ LaHat D, mulF D a (L.actG g v - v) = N • w := fun v hv => by
      obtain ⟨x, w', hw', rfl⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D N hN hNp v hv
      obtain ⟨v₁, hv₁, e₁⟩ := h x
      refine ⟨v₁ + mulF D a (L.actG g w' - w'), add_mem hv₁ (mulF_mem a (sub_mem (hg _ hw') hw')), ?_⟩
      have e₂ : mulF D a (L.actG g (inAf D x) - inAf D x) = N • v₁ := by
        rw [map_sub, ← actG_mulF, mulF_inAf, e₁]; abel
      have e₃ : L.actG g (inAf D x + N • w') - (inAf D x + N • w') =
          (L.actG g (inAf D x) - inAf D x) + N • (L.actG g w' - w') := by
        rw [map_add, map_nsmul, smul_sub]; abel
      rw [e₃, map_add, e₂, map_nsmul, smul_add]
    intro v hv
    have hu : L.actG g v - v ∈ LaHat D := sub_mem (hg v hv) hv
    obtain ⟨w₁, hw₁, e₁⟩ := step1 v hv
    obtain ⟨y, w, hw, e₂⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D N hN hNp _ hu
    have hdvd : ∃ u : D.La, algebraMap (𝓞 D.F) D.O a • y = N • u := by
      refine GlobalTheory.T.exists_latticeVector_eq_nsmul_of_adelic_nsmul p D N hN hNp (GlobalTheory.T.int_dvd_of_eq_nat_mul_integralAdeleAwayFromP p N hN hNp) _ ⟨w₁ - mulF D a w, sub_mem hw₁ (mulF_mem a hw), ?_⟩
      rw [e₂, map_add, mulF_inAf, map_nsmul] at e₁
      rw [smul_sub, ← e₁]; abel
    have hy : y ∈ wSub D 𝔞 1 := ((hLG p D a N 𝔞 hN hgen).1 y).1 hdvd
    rw [e₂]
    refine add_mem (wSub_inAf hy) ?_
    rw [← mulF_nat]
    exact mem_idHat hNa hw

end UpperTheory.Gal.Int.Geo.CRT

open UpperTheory.Gal.Int.Geo.CRT in
/- English proof (translation)
Introduce `hLG p _ D G L q r N₀ 𝔞 hc ⟨e, he⟩ g hg`. Take `⟨s, t, ht, est⟩` from `bezout hc e he`. Conclude with `⟨crt_part L N₀ 𝔞 s t ht est g, fun a N hN hNp hgen => gen_part hLG L 𝔞 g hg a N hN hNp hgen⟩`.
-/
theorem UpperTheory.congruenceCRT_of_latticeGen :
    LatGen → CongCRT := by
  intro hLG p _ D G L q r N₀ 𝔞 hc ⟨e, he⟩ g hg
  obtain ⟨s, t, ht, est⟩ := bezout hc e he
  exact ⟨crt_part L N₀ 𝔞 s t ht est g, fun a N hN hNp hgen => gen_part hLG L 𝔞 g hg a N hN hNp hgen⟩

end
