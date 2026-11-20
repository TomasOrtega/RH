import Formalism.WachLatticeTwists.DenseTopActions.DenseTopActionProofs.OneAddPowSubOne

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JW

open Matrix Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

section

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
  {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {W : NData S ι pr D} {As : Type} [CommRing As] {jS : As →+* (ι → A)} {r : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Phi, W.φ_smul]`.
-/
theorem Phi_smul (a : ι → A) (x : ι → D) :
    Phi W (a • x) = (fun i => S.φ (a (pr i))) • Phi W x := by
  funext i
  simp [Phi, W.φ_smul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Phi, Finset.sum_apply, map_sum]`.
-/
theorem Phi_sum {κ : Type} (s : Finset κ) (f : κ → ι → D) :
    Phi W (∑ k ∈ s, f k) = ∑ k ∈ s, Phi W (f k) := by
  funext i
  simp [Phi, Finset.sum_apply, map_sum]

/- English proof (translation)
Rewrite using `[lc, Phi_sum, lc]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Phi_smul]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `(hφs _ _).symm`.
-/
theorem Phi_lc (φs : As →+* As) (hφs : ∀ a i, jS (φs a) i = S.φ (jS a (pr i)))
    (b : Fin r → ι → D) (c : Fin r → As) :
    Phi W (lc jS b c) = lc jS (fun l => Phi W (b l)) (fun l => φs (c l)) := by
  rw [lc, Phi_sum, lc]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Phi_smul]
  congr 1
  funext i
  exact (hφs _ _).symm

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using h`. Consider the case `succ n ih`. Apply `ih` to reduce the goal to its premises. Apply `W.Q_bij.1` to reduce the goal to its premises.

Simplify using `only [smul_zero]`. Rewrite using `[smul_smul, ← pow_succ']`. Conclude with `h`.
-/
theorem Q_pow_inj (W : NData S ι pr D) (n : ℕ) (x : D) (h : S.Q ^ n • x = 0) : x = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply W.Q_bij.1
    simp only [smul_zero]
    rw [smul_smul, ← pow_succ']
    exact h

def SpPhi (W : NData S ι pr D) (jS : As →+* (ι → A)) (b : Fin r → ι → D) (z : ι → D) : Prop :=
  ∃ c : Fin r → As, z = lc jS (fun l => Phi W (b l)) c

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Take `⟨c', rfl⟩` from `h'`. Conclude with `⟨c + c', (lc_add _ _ _ _).symm⟩`.
-/
theorem SpPhi.add {b : Fin r → ι → D} {z z' : ι → D} (h : SpPhi W jS b z) (h' : SpPhi W jS b z') :
    SpPhi W jS b (z + z') := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨c', rfl⟩ := h'
  exact ⟨c + c', (lc_add _ _ _ _).symm⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, by simp [lc]⟩`.
-/
theorem SpPhi.zero {b : Fin r → ι → D} : SpPhi W jS b 0 := ⟨0, by simp [lc]⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using SpPhi.zero`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `(h a (Finset.mem_insert_self _ _)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
theorem SpPhi.sum {b : Fin r → ι → D} {κ : Type} (s : Finset κ) (f : κ → ι → D)
    (h : ∀ k ∈ s, SpPhi W jS b (f k)) : SpPhi W jS b (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SpPhi.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Conclude with `⟨a • c, (lc_smul _ _ _ _).symm⟩`.
-/
theorem SpPhi.smulAs {b : Fin r → ι → D} {z : ι → D} (a : As) (h : SpPhi W jS b z) :
    SpPhi W jS b (jS a • z) := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨a • c, (lc_smul _ _ _ _).symm⟩

/- English proof (translation)
Take `⟨c, hc⟩` from `hb.span x hx`. Use `⟨fun l => φs (c l), ?_⟩` and prove the remaining obligations. Rewrite using `[← Phi_lc φs hφs]`. Conclude with `congrArg _ hc`.
-/
theorem SpPhi.ofN (φs : As →+* As) (hφs : ∀ a i, jS (φs a) i = S.φ (jS a (pr i)))
    {b : Fin r → ι → D} (hb : BasisN W jS b) {x : ι → D} (hx : InN W x) :
    SpPhi W jS b (Phi W x) := by
  obtain ⟨c, hc⟩ := hb.span x hx
  refine ⟨fun l => φs (c l), ?_⟩
  rw [← Phi_lc φs hφs]
  exact congrArg _ hc

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Rewrite using `[← lc_smul_family]`. Use `SpPhi.sum _ _ fun k _ => SpPhi.smulAs _ ?_` and prove the remaining obligations. Establish `: (fun _ => algebraMap O A o : ι → A) • Phi W (b k) = Phi W ((fun _ => algebraMap O A o : ι → A) • b k)`. Rewrite using `[Phi_smul]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Use `show SpPhi W jS b ((fun _ => algebraMap O A o : ι → A) • Phi W (b k))`. Rewrite using `[this]`.

Conclude with `SpPhi.ofN φs hφs hb (inN_smul _ (hb.mem k))`.
-/
theorem SpPhi.smulO (φs : As →+* As) (hφs : ∀ a i, jS (φs a) i = S.φ (jS a (pr i)))
    {b : Fin r → ι → D} (hb : BasisN W jS b) {z : ι → D} (o : O) (h : SpPhi W jS b z) :
    SpPhi W jS b ((fun _ => algebraMap O A o : ι → A) • z) := by
  obtain ⟨c, rfl⟩ := h
  rw [← lc_smul_family]
  refine SpPhi.sum _ _ fun k _ => SpPhi.smulAs _ ?_
  have : (fun _ => algebraMap O A o : ι → A) • Phi W (b k)
      = Phi W ((fun _ => algebraMap O A o : ι → A) • b k) := by
    rw [Phi_smul]
    congr 1
    funext i
    simp
  show SpPhi W jS b ((fun _ => algebraMap O A o : ι → A) • Phi W (b k))
  rw [this]
  exact SpPhi.ofN φs hφs hb (inN_smul _ (hb.mem k))

/- English proof (translation)
Take `⟨n, c, o, rfl⟩` from `hG a`. Rewrite using `[Finset.sum_smul]`. Use `SpPhi.sum _ _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul]`. Conclude with `SpPhi.smulAs _ (SpPhi.smulO φs hφs hb _ h)`.
-/
theorem SpPhi.smulA (φs : As →+* As) (hφs : ∀ a i, jS (φs a) i = S.φ (jS a (pr i)))
    (hG : GenO O jS) {b : Fin r → ι → D} (hb : BasisN W jS b) {z : ι → D} (a : ι → A)
    (h : SpPhi W jS b z) : SpPhi W jS b (a • z) := by
  obtain ⟨n, c, o, rfl⟩ := hG a
  rw [Finset.sum_smul]
  refine SpPhi.sum _ _ fun k _ => ?_
  rw [mul_smul]
  exact SpPhi.smulAs _ (SpPhi.smulO φs hφs hb _ h)

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨y, hy, rfl⟩` from `hz`. Establish `: (Pi.single i (W.φ i y) : ι → D) = Phi W (Pi.single (pr i) y)`. Use function extensionality and compare the values at `i'`.

Distinguish the cases in `hi : i' = i`. Substitute `hi` using the available equality. Simplify using `[Phi]`. Establish `: pr i' ≠ pr i` using `fun h => hi (pr.injective h)`. Simplify using `[Phi, Pi.single_eq_of_ne hi, Pi.single_eq_of_ne this]`.

Rewrite using `[this]`. Use `SpPhi.ofN φs hφs hb fun i' => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i' = pr i`. Substitute `hi` using the available equality. Simplify using `using hy`.

Rewrite using `[Pi.single_eq_of_ne hi]`. Conclude with `(W.N i').zero_mem`. Consider the case `zero => rw [Pi.single_zero]`. Conclude with `SpPhi.zero`. Consider the case `add x y _ _ hx hy => rw [Pi.single_add]`.

Conclude with `hx.add hy`. Consider the case `smul a x _ hx`. Establish `: (Pi.single i (a • x) : ι → D) = (fun _ => a : ι → A) • Pi.single i x`. Use function extensionality and compare the values at `i'`. Distinguish the cases in `hi : i' = i`.

Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hi]`. Rewrite using `[this]`. Conclude with `SpPhi.smulA φs hφs hG hb _ hx`.
-/
theorem SpPhi.single [DecidableEq ι] (φs : As →+* As)
    (hφs : ∀ a i, jS (φs a) i = S.φ (jS a (pr i)))
    (hG : GenO O jS) {b : Fin r → ι → D} (hb : BasisN W jS b) (i : ι) (z : D)
    (hz : z ∈ Submodule.span A (W.φ i '' (W.N (pr i) : Set D))) :
    SpPhi W jS b (Pi.single i z) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    have : (Pi.single i (W.φ i y) : ι → D) = Phi W (Pi.single (pr i) y) := by
      funext i'
      by_cases hi : i' = i
      · subst hi
        simp [Phi]
      · have : pr i' ≠ pr i := fun h => hi (pr.injective h)
        simp [Phi, Pi.single_eq_of_ne hi, Pi.single_eq_of_ne this]
    rw [this]
    refine SpPhi.ofN φs hφs hb fun i' => ?_
    by_cases hi : i' = pr i
    · subst hi
      simpa using hy
    · rw [Pi.single_eq_of_ne hi]
      exact (W.N i').zero_mem
  | zero => rw [Pi.single_zero]; exact SpPhi.zero
  | add x y _ _ hx hy => rw [Pi.single_add]; exact hx.add hy
  | smul a x _ hx =>
    have : (Pi.single i (a • x) : ι → D) = (fun _ => a : ι → A) • Pi.single i x := by
      funext i'
      by_cases hi : i' = i
      · subst hi
        simp
      · simp [Pi.single_eq_of_ne hi]
    rw [this]
    exact SpPhi.smulA φs hφs hG hb _ hx

end

/- English proof (translation)
Introduce `ℓ _ O A _ _ _ S ι _ pr D _ _ _ _ W As AA WC _ _ _ _ jS φs jA io φ Gg _ H act r ρ πs C b M h M0 h0 Xi hπ hφs hG hb hP5 hM hh inv1 inv2`. Consider the cases of `nonempty_fintype ι`. Take `⟨-, hQ, -, -⟩` from `xi O A S ι As jS πs hπ`. Use `set ξ := xiOf S.ℓ S.s πs with hξ`. Establish `hQp : ∀ n i, jS (ξ ^ n) i = S.Q ^ n`.

Introduce `n i`. Rewrite using `[map_pow, Pi.pow_apply, hQ]`. Establish `hy : ∀ k, InN W (jS (ξ ^ M0) • Phi W (b k))`. Introduce `k i`. Establish `h1` using `hP5.1 i (b k (pr i)) (hb.mem k (pr i))`.

Establish `: (jS (ξ ^ M0) • Phi W (b k)) i = S.Q ^ (M0 - M i) • (S.Q ^ M i • W.φ i (b k (pr i)))`. Rewrite using `[Pi.smul_apply', hQp, smul_smul, ← pow_add, Nat.sub_add_cancel (hM i)]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `(W.N i).smul_mem _ h1`.

Take `⟨P1, hP1⟩` from `hb.coords _ hy`. Establish `hz : ∀ k, SpPhi W jS b (jS (ξ ^ h0) • b k)`. Introduce `k`. Establish `: jS (ξ ^ h0) • b k = ∑ i, Pi.single i (S.Q ^ h0 • b k i)`. Use function extensionality and compare the values at `i`.

Rewrite using `[Finset.sum_apply, Finset.sum_eq_single i]`. Rewrite using `[Pi.single_eq_same, Pi.smul_apply', hQp]`. Introduce `i' _ hi'`. Conclude with `Pi.single_eq_of_ne (Ne.symm hi') _`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Use `SpPhi.sum _ _ fun i _ => SpPhi.single φs hφs hG hb i _ ?_` and prove the remaining obligations. Establish `h2` using `hP5.2 i (b k i) (hb.mem k i)`. Establish `: S.Q ^ h0 • b k i = S.Q ^ (h0 - h i) • (S.Q ^ h i • b k i)`. Rewrite using `[smul_smul, ← pow_add, Nat.sub_add_cancel (hh i)]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ h2`. Use `choose Cm hCm using hz`. Establish `hCP : (Matrix.of Cm) * P1 = (ξ ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) As)`. Apply `Matrix.ext_row` to reduce the goal to its premises.

Introduce `k`. Use `show (Matrix.of Cm * P1) k = ((ξ ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) As)) k`. Apply `hb.uniq` to reduce the goal to its premises. Rewrite using `[Matrix.mul_apply_eq_vecMul, lc_vecMul]`. Establish `e1 : (fun l => lc jS b (P1 l)) = fun l => jS (ξ ^ M0) • Phi W (b l)`.

Use function extensionality and compare the values at `l`. Conclude with `(hP1 l).symm`. Rewrite using `[e1, lc_smul_family]`. Establish `e2 : lc jS (fun l => Phi W (b l)) (Matrix.of Cm k) = jS (ξ ^ h0) • b k` using `(hCm k).symm`. Rewrite using `[e2, smul_smul, ← map_mul, ← pow_add]`.

Establish `e3 : ((ξ ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) As)) k = Pi.single k (ξ ^ (M0 + h0))`. Use function extensionality and compare the values at `l`. Distinguish the cases in `hl : l = k`. Substitute `hl` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_eq_of_ne hl, Matrix.one_apply_ne (Ne.symm hl)]`. Rewrite using `[e3, lc_single]`. Establish `hPC : P1 * (Matrix.of Cm) = (ξ ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) As)`. Distinguish the cases in `hr : r = 0`. Substitute `hr` using the available equality.

Use extensionality with `i`. Conclude with `i.elim0`. Establish `k0 : Fin r` using `⟨0, Nat.pos_of_ne_zero hr⟩`. Use `mul_comm_of_regular _ _ _ (fun a ha => ?_) hCP` and prove the remaining obligations. Establish `h1 : jS a • b k0 = 0`.

Use function extensionality and compare the values at `i`. Apply `Q_pow_inj W (M0 + h0)` to reduce the goal to its premises. Use `congrFun (congrArg (fun t => jS t • b k0) ha) i` as an intermediate fact. Simplify using `only [map_mul, map_zero, zero_smul, Pi.zero_apply, mul_smul] at this`. Rewrite `this` using `[Pi.smul_apply', hQp]`.

Conclude with `this`. Establish `h2` using `hb.ind (Pi.single k0 a) (by`. Use `lc_single jS b k0 a` as an intermediate fact. Rewrite `this` using `[h1]`. Conclude with `this)`.

Use `congrFun h2 k0` as an intermediate fact. Simplify using `using this`. Establish `hmat : (P1.map jA).map io * xMat C b = (io (jA ξ)) ^ M0 • (xMat C b).map φ`. Rewrite using `[← mat_of_coords C b _ P1 hP1]`. Use extensionality with `k j`.

Rewrite using `[Matrix.of_apply, C.smul, C.phi, Matrix.smul_apply, Matrix.map_apply, Pi.smul_apply, map_pow, map_pow]`. Both sides reduce to the same expression. Use `⟨(xMat C b).map φ * Xi, P1, Matrix.of Cm, ?_, ?_, hPC⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, inv2, Matrix.mul_one]`. Rewrite using `[← Matrix.smul_mul, ← hmat, Matrix.mul_assoc, inv1, Matrix.mul_one]`.
-/
theorem w1 : HeightBoundFromFinite := by
  classical
  intro ℓ _ O A _ _ _ S ι _ pr D _ _ _ _ W As AA WC _ _ _ _ jS φs jA io φ Gg _ H act r ρ πs C b M h
    M0 h0 Xi hπ hφs hG hb hP5 hM hh inv1 inv2
  cases nonempty_fintype ι
  obtain ⟨-, hQ, -, -⟩ := xi O A S ι As jS πs hπ
  set ξ := xiOf S.ℓ S.s πs with hξ
  have hQp : ∀ n i, jS (ξ ^ n) i = S.Q ^ n := by
    intro n i
    rw [map_pow, Pi.pow_apply, hQ]

  have hy : ∀ k, InN W (jS (ξ ^ M0) • Phi W (b k)) := by
    intro k i
    have h1 := hP5.1 i (b k (pr i)) (hb.mem k (pr i))
    have : (jS (ξ ^ M0) • Phi W (b k)) i
        = S.Q ^ (M0 - M i) • (S.Q ^ M i • W.φ i (b k (pr i))) := by
      rw [Pi.smul_apply', hQp, smul_smul, ← pow_add, Nat.sub_add_cancel (hM i)]
      rfl
    rw [this]
    exact (W.N i).smul_mem _ h1
  obtain ⟨P1, hP1⟩ := hb.coords _ hy

  have hz : ∀ k, SpPhi W jS b (jS (ξ ^ h0) • b k) := by
    intro k
    have : jS (ξ ^ h0) • b k = ∑ i, Pi.single i (S.Q ^ h0 • b k i) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, Pi.smul_apply', hQp]
      · intro i' _ hi'
        exact Pi.single_eq_of_ne (Ne.symm hi') _
      · simp
    rw [this]
    refine SpPhi.sum _ _ fun i _ => SpPhi.single φs hφs hG hb i _ ?_
    have h2 := hP5.2 i (b k i) (hb.mem k i)
    have : S.Q ^ h0 • b k i = S.Q ^ (h0 - h i) • (S.Q ^ h i • b k i) := by
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel (hh i)]
    rw [this]
    exact Submodule.smul_mem _ _ h2
  choose Cm hCm using hz
  have hCP : (Matrix.of Cm) * P1 = (ξ ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) As) := by
    apply Matrix.ext_row
    intro k
    show (Matrix.of Cm * P1) k = ((ξ ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) As)) k
    apply hb.uniq
    rw [Matrix.mul_apply_eq_vecMul, lc_vecMul]
    have e1 : (fun l => lc jS b (P1 l)) = fun l => jS (ξ ^ M0) • Phi W (b l) := by
      funext l
      exact (hP1 l).symm
    rw [e1, lc_smul_family]
    have e2 : lc jS (fun l => Phi W (b l)) (Matrix.of Cm k) = jS (ξ ^ h0) • b k := (hCm k).symm
    rw [e2, smul_smul, ← map_mul, ← pow_add]
    have e3 : ((ξ ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) As)) k = Pi.single k (ξ ^ (M0 + h0)) := by
      funext l
      by_cases hl : l = k
      · subst hl; simp
      · simp [Pi.single_eq_of_ne hl, Matrix.one_apply_ne (Ne.symm hl)]
    rw [e3, lc_single]
  have hPC : P1 * (Matrix.of Cm) = (ξ ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) As) := by
    by_cases hr : r = 0
    · subst hr
      ext i
      exact i.elim0
    · have k0 : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
      refine mul_comm_of_regular _ _ _ (fun a ha => ?_) hCP
      have h1 : jS a • b k0 = 0 := by
        funext i
        apply Q_pow_inj W (M0 + h0)
        have := congrFun (congrArg (fun t => jS t • b k0) ha) i
        simp only [map_mul, map_zero, zero_smul, Pi.zero_apply, mul_smul] at this
        rw [Pi.smul_apply', hQp] at this
        exact this
      have h2 := hb.ind (Pi.single k0 a) (by
        have := lc_single jS b k0 a
        rw [h1] at this
        exact this)
      have := congrFun h2 k0
      simpa using this

  have hmat : (P1.map jA).map io * xMat C b = (io (jA ξ)) ^ M0 • (xMat C b).map φ := by
    rw [← mat_of_coords C b _ P1 hP1]
    ext k j
    rw [Matrix.of_apply, C.smul, C.phi, Matrix.smul_apply, Matrix.map_apply, Pi.smul_apply, map_pow,
      map_pow]
    rfl
  refine ⟨(xMat C b).map φ * Xi, P1, Matrix.of Cm, ?_, ?_, hPC⟩
  · rw [Matrix.mul_assoc, inv2, Matrix.mul_one]
  · rw [← Matrix.smul_mul, ← hmat, Matrix.mul_assoc, inv1, Matrix.mul_one]

end Formalism.RepresentationBoundsCohomology.JW
