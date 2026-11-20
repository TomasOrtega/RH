import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
Establish `hq0` using `GlobalTheory.TopStep.qOf_ne_zero (P := P)`. Establish `key : {z | z - a ∈ stdAt E n P} = {z | z - a' ∈ stdAt E n P} ↔ a - a' ∈ stdAt E n P`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h0 : a ∈ {z | z - a ∈ stdAt E n P}` using `by show a - a ∈ stdAt E n P`.

Rewrite using `[sub_self]`. Conclude with `zero_mem _`. Rewrite `h0` using `[h]`. Conclude with `h0`. Introduce `h`.

Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Use `add_mem hz h` as an intermediate fact.

Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Introduce `hz`. Use `sub_mem hz h` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis. Rewrite using `[key, GlobalTheory.TopStep.mem_stdAt]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `i`. Establish `hi` using `GlobalTheory.TopStep.mem_stdAt.1 ha i`. Establish `hi'` using `GlobalTheory.TopStep.mem_stdAt.1 ha' i`.

Use `show redP P ((((qOf P : ℕ) : E) • a) i) = redP P ((((qOf P : ℕ) : E) • a') i)`. Rewrite using `[← sub_eq_zero, ← GlobalTheory.TopStep.reduction_sub hi hi']`. Apply `GlobalTheory.TopStep.redP_eq_zero_of_div` to reduce the goal to its premises. Use `h i using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]`.

Clear the denominators using the available nonvanishing facts. Introduce `h i`. Establish `hi` using `GlobalTheory.TopStep.mem_stdAt.1 ha i`. Establish `hi'` using `GlobalTheory.TopStep.mem_stdAt.1 ha' i`. Establish `e` using `congrFun h i`.

Establish `h0 : redP P ((((qOf P : ℕ) : E) • a) i - (((qOf P : ℕ) : E) • a') i) = 0`. Rewrite using `[GlobalTheory.TopStep.reduction_sub hi hi']`. Conclude with `sub_eq_zero.2 e`. Use `GlobalTheory.TopStep.intAt_div_of_redP hq (GlobalTheory.TopStep.intAt_sub hi hi') h0` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]`. Clear the denominators using the available nonvanishing facts.
-/
theorem coset_eq_iff_redV (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {a a' : Sp E n}
    (ha : ((qOf P : ℕ) : E) • a ∈ stdAt E n P) (ha' : ((qOf P : ℕ) : E) • a' ∈ stdAt E n P) :
    {z | z - a ∈ stdAt E n P} = {z | z - a' ∈ stdAt E n P} ↔
      redV P (((qOf P : ℕ) : E) • a) = redV P (((qOf P : ℕ) : E) • a') := by
  have hq0 := GlobalTheory.TopStep.qOf_ne_zero (P := P)
  have key : {z | z - a ∈ stdAt E n P} = {z | z - a' ∈ stdAt E n P} ↔ a - a' ∈ stdAt E n P := by
    constructor
    · intro h
      have h0 : a ∈ {z | z - a ∈ stdAt E n P} := by
        show a - a ∈ stdAt E n P
        rw [sub_self]
        exact zero_mem _
      rw [h] at h0
      exact h0
    · intro h
      ext z
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hz
        have := add_mem hz h
        rwa [sub_add_sub_cancel] at this
      · intro hz
        have := sub_mem hz h
        rwa [sub_sub_sub_cancel_right] at this
  rw [key, GlobalTheory.TopStep.mem_stdAt]
  constructor
  · intro h
    funext i
    have hi := GlobalTheory.TopStep.mem_stdAt.1 ha i
    have hi' := GlobalTheory.TopStep.mem_stdAt.1 ha' i
    show redP P ((((qOf P : ℕ) : E) • a) i) = redP P ((((qOf P : ℕ) : E) • a') i)
    rw [← sub_eq_zero, ← GlobalTheory.TopStep.reduction_sub hi hi']
    apply GlobalTheory.TopStep.redP_eq_zero_of_div
    convert h i using 1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    field_simp
  · intro h i
    have hi := GlobalTheory.TopStep.mem_stdAt.1 ha i
    have hi' := GlobalTheory.TopStep.mem_stdAt.1 ha' i
    have e := congrFun h i
    have h0 : redP P ((((qOf P : ℕ) : E) • a) i - (((qOf P : ℕ) : E) • a') i) = 0 := by
      rw [GlobalTheory.TopStep.reduction_sub hi hi']
      exact sub_eq_zero.2 e
    have := GlobalTheory.TopStep.intAt_div_of_redP hq (GlobalTheory.TopStep.intAt_sub hi hi') h0
    convert this using 1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    field_simp

end Local

section Pt

open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

/- English proof (translation)
Establish `h` using `P.2`. Simplify using `only [rowSG, uSG, hQ, Finset.union_empty] at h`. Conclude with `h`.
-/
theorem mem_vGs_of_rowSG (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (P : rowSG Pr sel mu) : P.1 ∈ Pr.vGs := by
  have h := P.2
  simp only [rowSG, uSG, hQ, Finset.union_empty] at h
  exact h

/- English proof (translation)
Take `⟨y, hy, hY⟩` from `q.mem_ybSet h`. Use `⟨y, fun w hw => ?_, fun z => ?_⟩` and prove the remaining obligations. Use `(Formalism.L2.Col.mem_locLat _ _ _ _).1 hy ⟨w, Finset.mem_union_left _ hw⟩` as an intermediate fact. Simplify `this` using `[hw]`. Rewrite using `[hY, Set.mem_setOf_eq, Formalism.L2.Col.mem_locLat]`.

Prove the components needed by the constructor for the conclusion. Introduce `h w hw`. Simplify `h ⟨w, Finset.mem_union_left _ hw⟩` using `[hw]`. Introduce `h P`. Establish `hP` using `mem_vGs_of_rowSG hQ P`.

Simplify `h P.1 hP` using `[hP]`.
-/
theorem ptAt_coset (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (q : PtAt R sel mu cst u j) (h : j + 1 = R.m) :
    ∃ y : Sp X.E (R.N j), (∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) ∧
      ∀ z, z ∈ q.1.2 ↔ ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N := by
  obtain ⟨y, hy, hY⟩ := q.mem_ybSet h
  refine ⟨y, fun w hw => ?_, fun z => ?_⟩
  · have := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy ⟨w, Finset.mem_union_left _ hw⟩
    simpa [hw] using this
  · rw [hY, Set.mem_setOf_eq, Formalism.L2.Col.mem_locLat]
    constructor
    · intro h w hw
      simpa [hw] using h ⟨w, Finset.mem_union_left _ hw⟩
    · intro h P
      have hP := mem_vGs_of_rowSG hQ P
      simpa [hP] using h P.1 hP

/- English proof (translation)
Establish `hP` using `mem_vGs_of_rowSG hQ P`. Establish `hf` using `GlobalTheory.TopStep.liftFr_spec q.1.1.deco.2 ⟨P.1, hP⟩`. Establish `hfr : frsF sel mu q.1.1 P = q.1.1.deco.1.liftFr ⟨P.1, hP⟩`. Unfold `frsF`. Rewrite using `[dif_pos hP]`.

Use extensionality with `z`. Simplify using `only [cosetIn, Set.mem_setOf_eq, if_pos hP, pow_zero, inv_one, one_smul, hfr]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y', hy', hz⟩`. Establish `h1 : (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y' - (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y ∈ stdAt X.E (R.N j) P.1`.

Rewrite using `[← map_sub]`. Conclude with `(hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact (hY y').1 hy' P.1 hP)`. Use `add_mem hz h1` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Introduce `hz`.

Conclude with `⟨y, (hY y).2 fun w _ => by rw [sub_self]; exact zero_mem _, hz⟩`.
-/
theorem cosetIn_eq (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)}
    (hY : ∀ z, z ∈ q.1.2 ↔ ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (P : rowSG Pr sel mu) :
    cosetIn q P = {z | z - (q.1.1.deco.1.liftFr ⟨P.1, mem_vGs_of_rowSG hQ P⟩).symm y ∈ stdAt X.E (R.N j) P.1} := by
  have hP := mem_vGs_of_rowSG hQ P
  have hf := GlobalTheory.TopStep.liftFr_spec q.1.1.deco.2 ⟨P.1, hP⟩
  have hfr : frsF sel mu q.1.1 P = q.1.1.deco.1.liftFr ⟨P.1, hP⟩ := by
    unfold frsF
    rw [dif_pos hP]
  ext z
  simp only [cosetIn, Set.mem_setOf_eq, if_pos hP, pow_zero, inv_one, one_smul, hfr]
  constructor
  · rintro ⟨y', hy', hz⟩
    have h1 : (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y' - (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y ∈ stdAt X.E (R.N j) P.1 := by
      rw [← map_sub]
      exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact (hY y').1 hy' P.1 hP)
    have := add_mem hz h1
    rwa [sub_add_sub_cancel] at this
  · intro hz
    exact ⟨y, (hY y).2 fun w _ => by rw [sub_self]; exact zero_mem _, hz⟩

/- English proof (translation)
Establish `hd` using `q.1.1.deco.2`. Establish `hf` using `GlobalTheory.TopStep.liftFr_spec hd w`. Establish `hq` using `hy w.1 w.2`. Establish `key : q.1.1.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y) = redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y)`. Rewrite using `[← map_smul]`.

Establish `hs : (q.1.1.deco.1.liftFr w).symm (((qOf w.1 : ℕ) : X.E) • y) ∈ stdAt X.E _ w.1` using `(hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hq)`. Rewrite using `[← hf.2 _ hs, LinearEquiv.apply_symm_apply]`. Use extensionality with `v`. Simplify using `only [bar, Set.mem_setOf_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, hz, rfl⟩`. Rewrite using `[← key]`. Establish `ht : z - y ∈ q.1.1.deco.1.at w.1` using `(hY z).1 hz w.1 w.2`. Establish `e : ((qOf w.1 : ℕ) : X.E) • z = ((qOf w.1 : ℕ) : X.E) • y + ((qOf w.1 : ℕ) : X.E) • (z - y)`. Rewrite using `[← smul_add, add_sub_cancel]`.

Rewrite using `[e, hd.be_add w _ hq _ (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) ht), GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) ht, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]`. Introduce and unpack `rfl`. Conclude with `⟨y, (hY y).2 fun w _ => by rw [sub_self]; exact zero_mem _, key.symm⟩`.
-/
theorem bar_eq (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)}
    (hy : ∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N)
    (hY : ∀ z, z ∈ q.1.2 ↔ ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (w : Pr.vGs) :
    bar q w = {redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y)} := by
  have hd := q.1.1.deco.2
  have hf := GlobalTheory.TopStep.liftFr_spec hd w
  have hq := hy w.1 w.2
  have key : q.1.1.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y) =
      redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y) := by
    rw [← map_smul]
    have hs : (q.1.1.deco.1.liftFr w).symm (((qOf w.1 : ℕ) : X.E) • y) ∈ stdAt X.E _ w.1 :=
      (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hq)
    rw [← hf.2 _ hs, LinearEquiv.apply_symm_apply]
  ext v
  simp only [bar, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← key]
    have ht : z - y ∈ q.1.1.deco.1.at w.1 := (hY z).1 hz w.1 w.2
    have e : ((qOf w.1 : ℕ) : X.E) • z = ((qOf w.1 : ℕ) : X.E) • y + ((qOf w.1 : ℕ) : X.E) • (z - y) := by
      rw [← smul_add, add_sub_cancel]
    rw [e, hd.be_add w _ hq _ (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) ht),
      GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) ht, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]
  · rintro rfl
    exact ⟨y, (hY y).2 fun w _ => by rw [sub_self]; exact zero_mem _, key.symm⟩

/- English proof (translation)
Introduce `X Pr R sel S mu cst u j hQ hq q q'`. Distinguish the cases in `h : j + 1 = R.m`. Take `⟨y, hy, hY⟩` from `ptAt_coset hQ q h`. Take `⟨y', hy', hY'⟩` from `ptAt_coset hQ q' h`. Establish `hA : ∀ (p : PtAt R sel mu cst u j) (y : Sp X.E (R.N j)), (∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal p.1.1.deco.1.N) → ∀ w : Pr.vGs, ((qOf w.1 : ℕ) : X.E) • (p.1.1.deco.1.liftFr w).symm y ∈ stdAt X.E (R.N j) w.1`.

Introduce `p y hy w`. Establish `hf` using `GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 w`. Rewrite using `[← map_smul]`. Conclude with `(hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hy w.1 w.2)`. Rewrite using `[funext_iff, funext_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `H w`. Use `H ⟨w.1, Finset.mem_union_left _ w.2⟩` as an intermediate fact. Rewrite `this` using `[cosetIn_eq hQ q hY, cosetIn_eq hQ q' hY']`. Rewrite using `[bar_eq q hy hY, bar_eq q' hy' hY', Set.singleton_eq_singleton_iff]`.

Conclude with `(coset_eq_iff_redV (hq w.1 w.2) (hA q y hy w) (hA q' y' hy' w)).1 this`. Introduce `H P`. Establish `hP` using `mem_vGs_of_rowSG hQ P`. Use `H ⟨P.1, hP⟩` as an intermediate fact. Rewrite `this` using `[bar_eq q hy hY, bar_eq q' hy' hY', Set.singleton_eq_singleton_iff]`.

Rewrite using `[cosetIn_eq hQ q hY, cosetIn_eq hQ q' hY']`. Conclude with `(coset_eq_iff_redV (hq P.1 hP) (hA q y hy ⟨P.1, hP⟩) (hA q' y' hy' ⟨P.1, hP⟩)).2 this`. Establish `e : ∀ p : PtAt R sel mu cst u j, p.1.2 = ∅` using `fun p => by`. Use `p.2` as an intermediate fact. Rewrite `this` using `[ysAt_ys_of_ne sel mu cst h]`.

Conclude with `this`. Establish `h1 : ∀ p : PtAt R sel mu cst u j, cosetIn p = fun _ => ∅` using `fun p => by`. Use function extensionality and compare the values at `P`. Use extensionality with `z`. Simplify using `[cosetIn, e p]`.

Establish `h2 : ∀ p : PtAt R sel mu cst u j, bar p = fun _ => ∅` using `fun p => by`. Use function extensionality and compare the values at `w`. Use extensionality with `v`. Simplify using `[bar, e p]`. Rewrite using `[h1 q, h1 q', h2 q, h2 q']`.

Simplify using the standard rewrite rules.
-/
theorem cosetIn_eq_iff_bar_eq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ},
    QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) →
    ∀ q q' : PtAt R sel mu cst u j, cosetIn q = cosetIn q' ↔ MemChart.bar q = MemChart.bar q' := by
  intro X Pr R sel S mu cst u j hQ hq q q'
  by_cases h : j + 1 = R.m
  · obtain ⟨y, hy, hY⟩ := ptAt_coset hQ q h
    obtain ⟨y', hy', hY'⟩ := ptAt_coset hQ q' h
    have hA : ∀ (p : PtAt R sel mu cst u j) (y : Sp X.E (R.N j)),
        (∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal p.1.1.deco.1.N) → ∀ w : Pr.vGs,
        ((qOf w.1 : ℕ) : X.E) • (p.1.1.deco.1.liftFr w).symm y ∈ stdAt X.E (R.N j) w.1 := by
      intro p y hy w
      have hf := GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 w
      rw [← map_smul]
      exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hy w.1 w.2)
    rw [funext_iff, funext_iff]
    constructor
    · intro H w
      have := H ⟨w.1, Finset.mem_union_left _ w.2⟩
      rw [cosetIn_eq hQ q hY, cosetIn_eq hQ q' hY'] at this
      rw [bar_eq q hy hY, bar_eq q' hy' hY', Set.singleton_eq_singleton_iff]
      exact (coset_eq_iff_redV (hq w.1 w.2) (hA q y hy w) (hA q' y' hy' w)).1 this
    · intro H P
      have hP := mem_vGs_of_rowSG hQ P
      have := H ⟨P.1, hP⟩
      rw [bar_eq q hy hY, bar_eq q' hy' hY', Set.singleton_eq_singleton_iff] at this
      rw [cosetIn_eq hQ q hY, cosetIn_eq hQ q' hY']
      exact (coset_eq_iff_redV (hq P.1 hP) (hA q y hy ⟨P.1, hP⟩) (hA q' y' hy' ⟨P.1, hP⟩)).2 this
  · have e : ∀ p : PtAt R sel mu cst u j, p.1.2 = ∅ := fun p => by
      have := p.2
      rw [ysAt_ys_of_ne sel mu cst h] at this
      exact this
    have h1 : ∀ p : PtAt R sel mu cst u j, cosetIn p = fun _ => ∅ := fun p => by
      funext P
      ext z
      simp [cosetIn, e p]
    have h2 : ∀ p : PtAt R sel mu cst u j, bar p = fun _ => ∅ := fun p => by
      funext w
      ext v
      simp [bar, e p]
    rw [h1 q, h1 q', h2 q, h2 q']
    simp

end Pt

end GlobalTheory.Mem.Col2.MemChart
