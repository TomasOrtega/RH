import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReferenceTupleOffPrimesEmpty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatEqOfCarries
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiAtTransport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrsFBaseEqSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesPreimageUnderLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Formalism.LocalToGlobal.Columns.FixEColLevSym
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivFr

noncomputable section

namespace GlobalTheory.PenChart

/- English proof (translation)
Establish `h1 : ∀ (q : D) (g₀ : G), (fun r => ∃ g : G, r = f (g • g₀ • q)) = fun r => ∃ g : G, r = f (g • q)` using `fun q g₀ => by`. Use function extensionality and compare the values at `r`. Use `propext ⟨fun ⟨g, e⟩ => ⟨g * g₀, by rw [mul_smul]; exact e⟩, fun ⟨g, e⟩ => ⟨g * g₀⁻¹, by` and prove the remaining obligations. Rewrite using `[mul_smul, inv_smul_smul]`. Conclude with `e⟩⟩`.

Establish `h2 : ∀ q : D, f (GlobalTheory.Mem.Col2.prefRep pref (Quotient.mk (MulAction.orbitRel G D) q)) = Classical.epsilon (p` using `fun r => ∃ g : G, r = f (g • q)) (h := ⟨f q⟩) := fun q => by`. Establish `hex : ∃ p, Quotient.mk (MulAction.orbitRel G D) p = Quotient.mk (MulAction.orbitRel G D) q ∧ pref p`. Take `⟨g, hg⟩` from `Classical.epsilon_spec (p := fun r => ∃ g : G, r = f (g • q)) ⟨f q, 1, by rw [one_smul]⟩`. Use `⟨g • q, Quotient.sound ⟨g, rfl⟩, (h _).2 ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`.

Conclude with `hg.symm`. Unfold `GlobalTheory.Mem.Col2.prefRep`. Rewrite using `[dif_pos hex]`. Take `⟨g, hg⟩ : ∃ g : G, g • q = hex.choose` from `Quotient.exact hex.choose_spec.1`. Establish `h3` using `(h _).1 hex.choose_spec.2`.

Rewrite using `[h3, ← hg, h1]`. Rewrite using `[h2, h2]`. Simplify using `only [hd]`.
-/
theorem normal_rep {G D A : Type} [Group G] [MulAction G D] (f : D → A) (pref : D → Prop)
    (h : ∀ q, pref q ↔ f q = Classical.epsilon (p := fun r => ∃ g : G, r = f (g • q)) (h := ⟨f q⟩))
    (d d' : D) (hd : ∀ g : G, f (g • d') = f (g • d)) :
    f (GlobalTheory.Mem.Col2.prefRep pref (Quotient.mk (MulAction.orbitRel G D) d')) =
      f (GlobalTheory.Mem.Col2.prefRep pref (Quotient.mk (MulAction.orbitRel G D) d)) := by
  have h1 : ∀ (q : D) (g₀ : G), (fun r => ∃ g : G, r = f (g • g₀ • q)) = fun r => ∃ g : G, r = f (g • q) := fun q g₀ => by
    funext r
    refine propext ⟨fun ⟨g, e⟩ => ⟨g * g₀, by rw [mul_smul]; exact e⟩, fun ⟨g, e⟩ => ⟨g * g₀⁻¹, by
      rw [mul_smul, inv_smul_smul]; exact e⟩⟩
  have h2 : ∀ q : D, f (GlobalTheory.Mem.Col2.prefRep pref (Quotient.mk (MulAction.orbitRel G D) q)) =
      Classical.epsilon (p := fun r => ∃ g : G, r = f (g • q)) (h := ⟨f q⟩) := fun q => by
    have hex : ∃ p, Quotient.mk (MulAction.orbitRel G D) p = Quotient.mk (MulAction.orbitRel G D) q ∧ pref p := by
      obtain ⟨g, hg⟩ := Classical.epsilon_spec (p := fun r => ∃ g : G, r = f (g • q)) ⟨f q, 1, by rw [one_smul]⟩
      refine ⟨g • q, Quotient.sound ⟨g, rfl⟩, (h _).2 ?_⟩
      rw [h1]
      exact hg.symm
    unfold GlobalTheory.Mem.Col2.prefRep
    rw [dif_pos hex]
    obtain ⟨g, hg⟩ : ∃ g : G, g • q = hex.choose := Quotient.exact hex.choose_spec.1
    have h3 := (h _).1 hex.choose_spec.2
    rw [h3, ← hg, h1]
  rw [h2, h2]
  simp only [hd]

section Local

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2
open scoped Classical

section Vec

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
Unfold `Loc.eN`. Use `split_ifs`. Simplify using `using GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P 1`. Simplify using `using GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P 0`.
-/
theorem intAt_eN (k : ℕ) (l : Fin n) : IntAt P (Loc.eN E n k l) := by
  unfold Loc.eN
  split_ifs
  · simpa using GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P 1
  · simpa using GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P 0

/- English proof (translation)
Use function extensionality and compare the values at `l`. Unfold `redV Loc.eN`. Use `split_ifs`. Conclude with `redP_one`. Conclude with `redP_zero`.
-/
theorem redV_eN (k : ℕ) : redV P (Loc.eN E n k) = Loc.eN (𝓞 E ⧸ P.asIdeal) n k := by
  funext l
  unfold redV Loc.eN
  split_ifs
  · exact redP_one
  · exact redP_zero

/- English proof (translation)
Use `TopStep.mem_stdAt.2 fun l => ?_` and prove the remaining obligations. Establish `h` using `TopStep.intAt_div_of_redP hq (TopStep.intAt_sub (hx l) (intAt_eN k l)) ((TopStep.reduction_sub (hx l) (intAt_eN k l)).trans (sub_eq_zero.2 (congrFun (hr.trans (redV_eN k).symm) l)))`. Rewrite `h` using `[div_eq_inv_mul]`. Then use the resulting hypothesis.
-/
theorem inv_smul_sub_mem (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {k : ℕ} {x : Sp E n} (hx : ∀ l, IntAt P (x l))
    (hr : redV P x = Loc.eN (𝓞 E ⧸ P.asIdeal) n k) : (qOf P : E)⁻¹ • (x - Loc.eN E n k) ∈ stdAt E n P := by
  refine TopStep.mem_stdAt.2 fun l => ?_
  have h := TopStep.intAt_div_of_redP hq (TopStep.intAt_sub (hx l) (intAt_eN k l))
    ((TopStep.reduction_sub (hx l) (intAt_eN k l)).trans (sub_eq_zero.2 (congrFun (hr.trans (redV_eN k).symm) l)))
  rwa [div_eq_inv_mul] at h

end Vec

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

def Good (p : PtAt R sel mu cst u j) : Prop :=
  ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → (qOf P.1 : X.E)⁻¹ • Loc.eN X.E (R.N j) R.k ∈ cosetIn p P

/- English proof (translation)
Simplify using `only [cosetIn, if_pos hP, pow_zero, inv_one, one_smul, Set.mem_setOf_eq]`.
-/
theorem mem_cosetIn {p : PtAt R sel mu cst u j} {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs) {z : Sp X.E (R.N j)} :
    z ∈ cosetIn p P ↔ ∃ y ∈ p.1.2, z - (frsF sel mu p.1.1 P).symm y ∈ stdAt X.E (R.N j) P.1 := by
  simp only [cosetIn, if_pos hP, pow_zero, inv_one, one_smul, Set.mem_setOf_eq]

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, p.repY_mem h, by rw [sub_self, smul_zero]; exact zero_mem _⟩`.
-/
theorem rep_mem (h : j + 1 = R.m) (p : PtAt R sel mu cst u j) (P : rowSG Pr sel mu) :
    (frsF sel mu p.1.1 P).symm (repY p.1.2) ∈ cosetIn p P :=
  ⟨_, p.repY_mem h, by rw [sub_self, smul_zero]; exact zero_mem _⟩

/- English proof (translation)
Take `⟨y, hy, h2⟩` from `hz`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Use `add_mem h h2` as an intermediate fact. Rewrite `this` using `[← smul_add, sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem mem_of_sub {p : PtAt R sel mu cst u j} {P : rowSG Pr sel mu} {z z' : Sp X.E (R.N j)} (hz : z ∈ cosetIn p P)
    (h : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (z' - z) ∈ stdAt X.E (R.N j) P.1) : z' ∈ cosetIn p P := by
  obtain ⟨y, hy, h2⟩ := hz
  refine ⟨y, hy, ?_⟩
  have := add_mem h h2
  rwa [← smul_add, sub_add_sub_cancel] at this

/- English proof (translation)
The claim follows from `TopStep.mem_stdAt.2 fun l => GlobalTheory.TwU.AtTrue.Cl.sameCoset_of_mem_cosetIn p h P hz' hz l`.
-/
theorem sub_of_mem (h : j + 1 = R.m) {p : PtAt R sel mu cst u j} {P : rowSG Pr sel mu} {z z' : Sp X.E (R.N j)} (hz : z ∈ cosetIn p P)
    (hz' : z' ∈ cosetIn p P) :
    ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (z' - z) ∈ stdAt X.E (R.N j) P.1 :=
  TopStep.mem_stdAt.2 fun l => GlobalTheory.TwU.AtTrue.Cl.sameCoset_of_mem_cosetIn p h P hz' hz l

/- English proof (translation)
The claim follows from `Set.Subset.antisymm (fun _ hx => mem_of_sub hz' (sub_of_mem h hz hx)) fun _ hx => mem_of_sub hz (sub_of_mem h hz' hx)`.
-/
theorem cosetIn_eq_of_mem (h : j + 1 = R.m) {p p' : PtAt R sel mu cst u j} {P : rowSG Pr sel mu}
    {z : Sp X.E (R.N j)} (hz : z ∈ cosetIn p P) (hz' : z ∈ cosetIn p' P) : cosetIn p P = cosetIn p' P :=
  Set.Subset.antisymm (fun _ hx => mem_of_sub hz' (sub_of_mem h hz hx)) fun _ hx => mem_of_sub hz (sub_of_mem h hz' hx)

/- English proof (translation)
Establish `hq0 : (qOf P.1 : X.E) ≠ 0` using `GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1`. Establish `h1` using `inv_smul_sub_mem (x := (qOf P.1 : X.E) • (frsF sel mu p.1.1 P).symm (repY p.1.2)) (k := R.k) hq (fun l => (hp l).1) (funext fun l => (hp l).2)`. Use `(mem_cosetIn hP).2 ⟨_, p.repY_mem h, ?_⟩` and prove the remaining obligations. Rewrite `h1` using `[smul_sub, inv_smul_smul₀ hq0]`. Simplify using `using neg_mem h1`.
-/
theorem mem_cosetIn_of_res (h : j + 1 = R.m) (p : PtAt R sel mu cst u j) {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs)
    (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (hp : ∀ l, IntAt P.1 ((qOf P.1 : X.E) * (frsF sel mu p.1.1 P).symm (repY p.1.2) l) ∧
      redP P.1 ((qOf P.1 : X.E) * (frsF sel mu p.1.1 P).symm (repY p.1.2) l) = if l.1 = R.k then 1 else 0) :
    (qOf P.1 : X.E)⁻¹ • Loc.eN X.E (R.N j) R.k ∈ cosetIn p P := by
  have hq0 : (qOf P.1 : X.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
  have h1 := inv_smul_sub_mem (x := (qOf P.1 : X.E) • (frsF sel mu p.1.1 P).symm (repY p.1.2)) (k := R.k) hq (fun l => (hp l).1)
    (funext fun l => (hp l).2)
  refine (mem_cosetIn hP).2 ⟨_, p.repY_mem h, ?_⟩
  rw [smul_sub, inv_smul_smul₀ hq0] at h1
  simpa using neg_mem h1

variable (Λ : LevFam X.E X.K (R.N j) Pr.vGs) (Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))

/- English proof (translation)
Introduce `P hP`. Take `⟨y, hy, h1⟩` from `(mem_cosetIn hP).1 (hp P hP)`. Take `⟨κ, hκ, hr⟩` from `frsF_smul sel mu p.1.1 Λ Θ g P hP`. Establish `he : Loc.eN X.E (R.N j) R.k ∈ stdAt X.E (R.N j) P.1` using `TopStep.mem_stdAt.2 (intAt_eN _)`. Establish `h2` using `inv_smul_sub_mem (x := κ.1 (Loc.eN X.E (R.N j) R.k)) (k := R.k) (hq P) (TopStep.mem_stdAt.1 ((κ.2 _).2 he)) (by`.

Rewrite using `[hr _ he, redV_eN]`. Conclude with `hΛ _ (inv_mem g.2.1.2) ⟨P.1, hP⟩)`. Use `(mem_cosetIn hP).2 ⟨g.1.1 y, e2 ▸ ⟨y, hy, rfl⟩, (κ.2 _).1 ?_⟩` and prove the remaining obligations. Establish `e : κ.1 ((frsF sel mu p'.1.1 P).symm (g.1.1 y)) = (frsF sel mu p.1.1 P).symm y`. Rewrite using `[LinearEquiv.eq_symm_apply]`.

Apply `g.1.1.injective` to reduce the goal to its premises. Establish `h3` using `(frsF sel mu p'.1.1 P).apply_symm_apply (g.1.1 y)`. Rewrite `h3`, the goal using `[e1]`. Rewrite `h3` using `[hκ]`. Rewrite using `[hκ]`.

Conclude with `h3`. Rewrite using `[map_sub, e, map_smul]`. Use `add_mem h2 h1 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem good_smul (hq : ∀ P : rowSG Pr sel mu, ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (hΛ : ∀ h ∈ Λ.grp, ∀ w : Pr.vGs, (h w).1.mulVec (Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k) =
      Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k) (g : FrmG Λ Θ) (p p' : PtAt R sel mu cst u j)
    (e1 : p'.1.1 = g • p.1.1) (e2 : p'.1.2 = (fun v => g.1.1 v) '' p.1.2) (hp : Good p) : Good p' := by
  intro P hP
  obtain ⟨y, hy, h1⟩ := (mem_cosetIn hP).1 (hp P hP)
  obtain ⟨κ, hκ, hr⟩ := frsF_smul sel mu p.1.1 Λ Θ g P hP
  have he : Loc.eN X.E (R.N j) R.k ∈ stdAt X.E (R.N j) P.1 := TopStep.mem_stdAt.2 (intAt_eN _)
  have h2 := inv_smul_sub_mem (x := κ.1 (Loc.eN X.E (R.N j) R.k)) (k := R.k) (hq P) (TopStep.mem_stdAt.1 ((κ.2 _).2 he)) (by
    rw [hr _ he, redV_eN]
    exact hΛ _ (inv_mem g.2.1.2) ⟨P.1, hP⟩)
  refine (mem_cosetIn hP).2 ⟨g.1.1 y, e2 ▸ ⟨y, hy, rfl⟩, (κ.2 _).1 ?_⟩
  have e : κ.1 ((frsF sel mu p'.1.1 P).symm (g.1.1 y)) = (frsF sel mu p.1.1 P).symm y := by
    rw [LinearEquiv.eq_symm_apply]
    apply g.1.1.injective
    have h3 := (frsF sel mu p'.1.1 P).apply_symm_apply (g.1.1 y)
    rw [e1] at h3 ⊢
    rw [hκ] at h3
    rw [hκ]
    exact h3
  rw [map_sub, e, map_smul]
  convert add_mem h2 h1 using 1
  rw [smul_sub]
  abel

/- English proof (translation)
Use `set κ := g.2.2.1 ⟨P.1, hQ⟩ with hκ`. Establish `hf : ∀ y, (frsF sel mu p'.1.1 P).symm (g.1.1 y) = κ.1 ((frsF sel mu p.1.1 P).symm y)` using `fun y => by`. Rewrite using `[LinearEquiv.symm_apply_eq, e1]`. Unfold `frsF`. Rewrite using `[dif_neg hP, dif_neg hP]`.

Use `show _ = g.1.1 (p.1.1.fr ⟨P.1, hQ⟩ (κ.1.symm (κ.1 ((p.1.1.fr ⟨P.1, hQ⟩).symm y))))`. Rewrite using `[LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]`. Simplify using `only [cosetIn, Set.mem_setOf_eq, e2]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨y, hy, rfl⟩, h⟩`.

Rewrite `h` using `[hf, ← map_sub, ← map_smul]`. Conclude with `⟨y, hy, (κ.2 _).1 h⟩`. Introduce and unpack `⟨y, hy, h⟩`. Use `⟨_, ⟨y, hy, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, ← map_sub, ← map_smul]`.

Conclude with `(κ.2 _).2 h`.
-/
theorem mem_cosetIn_smul (g : FrmG Λ Θ) (p p' : PtAt R sel mu cst u j)
    (e1 : p'.1.1 = g • p.1.1) (e2 : p'.1.2 = (fun v => g.1.1 v) '' p.1.2) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K)) (z : Sp X.E (R.N j)) :
    (g.2.2.1 ⟨P.1, hQ⟩).1 z ∈ cosetIn p' P ↔ z ∈ cosetIn p P := by
  set κ := g.2.2.1 ⟨P.1, hQ⟩ with hκ
  have hf : ∀ y, (frsF sel mu p'.1.1 P).symm (g.1.1 y) = κ.1 ((frsF sel mu p.1.1 P).symm y) := fun y => by
    rw [LinearEquiv.symm_apply_eq, e1]
    unfold frsF
    rw [dif_neg hP, dif_neg hP]
    show _ = g.1.1 (p.1.1.fr ⟨P.1, hQ⟩ (κ.1.symm (κ.1 ((p.1.1.fr ⟨P.1, hQ⟩).symm y))))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  simp only [cosetIn, Set.mem_setOf_eq, e2]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩
    rw [hf, ← map_sub, ← map_smul] at h
    exact ⟨y, hy, (κ.2 _).1 h⟩
  · rintro ⟨y, hy, h⟩
    refine ⟨_, ⟨y, hy, rfl⟩, ?_⟩
    rw [hf, ← map_sub, ← map_smul]
    exact (κ.2 _).2 h

/- English proof (translation)
Set `z' : rowSG Pr sel mu → Sp X.E (R.N j)` to `fun P => if P.1 ∈ Pr.vGs then (qOf P.1 : X.E)⁻¹ • Loc.eN X.E (R.N j) R.k else z P`. Take `⟨y, hy⟩` from `GlobalTheory.CplCosetPt.exists_sameCoset_frames sel mu cst (fun P => frsF sel mu d P) z'`. Establish `hd : ∀ P, ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • ((frsF sel mu d P).symm y - z' P) ∈ stdAt X.E (R.N j) P.1` using `fun P => TopStep.mem_stdAt.2 fun l => hy P l`. Establish `hy' : y ∈ locLat (rowSG Pr sel mu) d.deco.1.N (fun P => if P.1 ∈ Pr.vGs then -1 else -(cst.M : ℤ))`. Use `(mem_locLat _ _ _ _).2 fun P => ?_` and prove the remaining obligations.

Establish `hq0 : (qOf P.1 : X.E) ≠ 0` using `GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1`. Establish `hn : ∀ (n : ℕ) v, v ∈ stdAt X.E (R.N j) P.1 → (qOf P.1 : X.E) ^ n • v ∈ stdAt X.E (R.N j) P.1` using `fun n v hv => by`. Rewrite using `[← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`. Conclude with `nsmul_mem hv _`. Establish `h0` using `hd P`.

Distinguish the cases in `hP : P.1 ∈ Pr.vGs`. Simplify using `only [z', if_pos hP, pow_zero, inv_one, one_smul] at h0`. Establish `h2` using `GlobalTheory.BaseCosetPt.frsF_mem d P (add_mem (hn 1 _ h0) (TopStep.mem_stdAt.2 (intAt_eN R.k)))`. Rewrite `h2` using `[pow_one, smul_sub, smul_inv_smul₀ hq0, sub_add_cancel, map_smul, LinearEquiv.apply_symm_apply]`. Simplify `h2` using `[hP]`.

Simplify using `only [z', if_neg hP] at h0`. Establish `h2` using `GlobalTheory.BaseCosetPt.frsF_mem d P (add_mem (hn (cst.M + cst.M) _ h0) (hz P hP))`. Rewrite `h2` using `[smul_smul, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), mul_one, smul_sub, sub_add_cancel, map_smul, LinearEquiv.apply_symm_apply]`. Simplify `h2` using `[hP]`. Establish `key : ∀ p : PtAt R sel mu cst u j, p.1.1 = d → y ∈ p.1.2 → ∀ P, z' P ∈ cosetIn p P`.

Introduce and unpack `p rfl hp P`. Use `⟨y, hp, ?_⟩` and prove the remaining obligations. Use `neg_mem (hd P)` as an intermediate fact. Rewrite `this` using `[← smul_neg, neg_sub]`. Then use the resulting hypothesis. Set `p : PtAt R sel mu cst u j` to `⟨(d, {z | z - y ∈ locLat (rowSG Pr sel mu) d.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}), by`.

Rewrite using `[ysAt_ys_of_eq sel mu cst h]`. Conclude with `⟨y, hy', rfl⟩⟩`. Establish `hp` using `key p rfl (by simp [p])`. Use `⟨p, fun P hP => ?_, fun P hP => ?_⟩` and prove the remaining obligations. Simplify `hp P` using `only [z', if_pos hP]`.

Simplify `hp P` using `only [z', if_neg hP]`.
-/
theorem exists_pt (h : j + 1 = R.m) (d : ChPt (R := R) sel mu u j) (z : rowSG Pr sel mu → Sp X.E (R.N j))
    (hz : ∀ P, P.1 ∉ Pr.vGs → (qOf P.1 : X.E) ^ cst.M • z P ∈ stdAt X.E (R.N j) P.1) :
    ∃ p : PtAt R sel mu cst u j, Good p ∧ ∀ P, P.1 ∉ Pr.vGs → z P ∈ cosetIn p P := by
  let z' : rowSG Pr sel mu → Sp X.E (R.N j) := fun P => if P.1 ∈ Pr.vGs then (qOf P.1 : X.E)⁻¹ • Loc.eN X.E (R.N j) R.k else z P
  obtain ⟨y, hy⟩ := GlobalTheory.CplCosetPt.exists_sameCoset_frames sel mu cst (fun P => frsF sel mu d P) z'
  have hd : ∀ P, ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • ((frsF sel mu d P).symm y - z' P) ∈
      stdAt X.E (R.N j) P.1 := fun P => TopStep.mem_stdAt.2 fun l => hy P l
  have hy' : y ∈ locLat (rowSG Pr sel mu) d.deco.1.N (fun P => if P.1 ∈ Pr.vGs then -1 else -(cst.M : ℤ)) := by
    refine (mem_locLat _ _ _ _).2 fun P => ?_
    have hq0 : (qOf P.1 : X.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
    have hn : ∀ (n : ℕ) v, v ∈ stdAt X.E (R.N j) P.1 → (qOf P.1 : X.E) ^ n • v ∈ stdAt X.E (R.N j) P.1 := fun n v hv => by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
      exact nsmul_mem hv _
    have h0 := hd P
    by_cases hP : P.1 ∈ Pr.vGs
    · simp only [z', if_pos hP, pow_zero, inv_one, one_smul] at h0
      have h2 := GlobalTheory.BaseCosetPt.frsF_mem d P (add_mem (hn 1 _ h0) (TopStep.mem_stdAt.2 (intAt_eN R.k)))
      rw [pow_one, smul_sub, smul_inv_smul₀ hq0, sub_add_cancel, map_smul, LinearEquiv.apply_symm_apply] at h2
      simpa [hP] using h2
    · simp only [z', if_neg hP] at h0
      have h2 := GlobalTheory.BaseCosetPt.frsF_mem d P (add_mem (hn (cst.M + cst.M) _ h0) (hz P hP))
      rw [smul_smul, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), mul_one, smul_sub, sub_add_cancel, map_smul,
        LinearEquiv.apply_symm_apply] at h2
      simpa [hP] using h2
  have key : ∀ p : PtAt R sel mu cst u j, p.1.1 = d → y ∈ p.1.2 → ∀ P, z' P ∈ cosetIn p P := by
    rintro p rfl hp P
    refine ⟨y, hp, ?_⟩
    have := neg_mem (hd P)
    rwa [← smul_neg, neg_sub] at this
  let p : PtAt R sel mu cst u j :=
    ⟨(d, {z | z - y ∈ locLat (rowSG Pr sel mu) d.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}), by
      rw [ysAt_ys_of_eq sel mu cst h]
      exact ⟨y, hy', rfl⟩⟩
  have hp := key p rfl (by simp [p])
  refine ⟨p, fun P hP => ?_, fun P hP => ?_⟩
  · simpa only [z', if_pos hP] using hp P
  · simpa only [z', if_neg hP] using hp P

end Local

section True

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.AdForm
open scoped Classical
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {u : B.Word} {a : I.ι} {j : ℕ}

/- English proof (translation)
Take `rfl : j = B.R.m - 2 + 1` from `by have := B.R.two_le_m; omega`. Take `⟨b₀, hb⟩` from `(hI.idx_ok a).last_uniq`. Rewrite using `[← b.of_get (by omega) (by omega), ← b'.of_get (by omega) (by omega), hb (b.get _), hb (b'.get _)]`.
-/
theorem idx_eq (hI : I.Ok) (hj : j + 1 = B.R.m) (b b' : Idx I.sel (I.tup a) (I.idx a) j) : b = b' := by
  obtain rfl : j = B.R.m - 2 + 1 := by have := B.R.two_le_m; omega
  obtain ⟨b₀, hb⟩ := (hI.idx_ok a).last_uniq
  rw [← b.of_get (by omega) (by omega), ← b'.of_get (by omega) (by omega), hb (b.get _), hb (b'.get _)]

abbrev levQ (I : TC B X) (a : I.ι) (j : ℕ) (b : Idx I.sel (I.tup a) (I.idx a) j) :=
  levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b

/- English proof (translation)
Establish `hΛ : levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = colLevSym I.Ch j`. Establish `e : ∀ al, (I.idx a).levG j al = colLevSym I.Ch j`. Rewrite using `[(ht a).2]`. Conclude with `fun _ => rfl`. Unfold `levGAt`.

Rewrite using `[← b.some_get (by omega)]`. Conclude with `e _`. Use `good_smul (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b) (levQ I a j b) (fun P => (degOne_of_ok hI a P).2) ?_ g p _ rfl rfl hp` and prove the remaining obligations. Rewrite using `[hΛ]`. Take `⟨m2, rfl⟩ : ∃ m2, j = m2 + 1` from `⟨j - 1, by have := B.R.two_le_m; omega⟩`.

Conclude with `fixE_colLevSym I.Ch hj.symm`.
-/
theorem good_act (hI : I.Ok) (ht : I.IsTw) (hj : j + 1 = B.R.m) (b : (I.stp u a j).β) (g : (I.stp u a j).G b) (p : (I.stp u a j).D b)
    (hp : Good p) : Good ((I.stp u a j).act b g p) := by
  have hΛ : levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = colLevSym I.Ch j := by
    have e : ∀ al, (I.idx a).levG j al = colLevSym I.Ch j := by
      rw [(ht a).2]
      exact fun _ => rfl
    unfold levGAt
    rw [← b.some_get (by omega)]
    exact e _
  refine good_smul (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b) (levQ I a j b) (fun P => (degOne_of_ok hI a P).2) ?_ g p _ rfl rfl hp
  rw [hΛ]
  obtain ⟨m2, rfl⟩ : ∃ m2, j = m2 + 1 := ⟨j - 1, by have := B.R.two_le_m; omega⟩
  exact fixE_colLevSym I.Ch hj.symm

/- English proof (translation)
The claim follows from `mem_cosetIn_smul (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b) (levQ I a j b) g p _ rfl rfl P hP hQ z`.
-/
theorem mem_act (b : (I.stp u a j).β) (g : (I.stp u a j).G b) (p : (I.stp u a j).D b) (P : rowSG (B.primes X) I.sel (I.tup a))
    (hP : P.1 ∉ (B.primes X).vGs) (hQ : P.1 ∈ I.Q a) (z) :
    (g.2.2.1 ⟨P.1, hQ⟩).1 z ∈ cosetIn ((I.stp u a j).act b g p) P ↔ z ∈ cosetIn p P :=
  mem_cosetIn_smul (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b) (levQ I a j b) g p _ rfl rfl P hP hQ z

/- English proof (translation)
Use `@normal_rep ((I.stp0 u a j).G b) ((I.stp0 u a j).D b) _ _ ((I.stp0 u a j).actD b) (fun q => cosetIn q) (I.pref u a j b) (fun q => ⟨fun hq => hq.2.1 hj, fun hq => ⟨fun h0 => by have := B.R.two_le_m; omega, fun _ => hq, fun h0 => by omega⟩⟩) d d' fun g => funext fun P => ?_` and prove the remaining obligations. Distinguish the cases in `hP : P.1 ∈ (B.primes X).vGs`. Conclude with `cosetIn_eq_of_mem hj (good_act hI ht hj b g d' hd' P hP) (good_act hI ht hj b g d hd P hP)`. Establish `hQ : P.1 ∈ I.Q a` using `(Finset.mem_union.mp P.2).resolve_left hP`. Establish `h1` using `rep_mem hj d P`.

Conclude with `cosetIn_eq_of_mem hj ((mem_act b g d' P hP hQ _).2 (h ▸ h1)) ((mem_act b g d P hP hQ _).2 h1)`.
-/
theorem rep_congr (hI : I.Ok) (ht : I.IsTw) (hj : j + 1 = B.R.m) (b : (I.stp u a j).β) (d d' : (I.stp u a j).D b) (hd : Good d)
    (hd' : Good d') (h : cosetIn d = cosetIn d') :
    cosetIn ((I.stp u a j).rep ((I.stp u a j).cl b d')) = cosetIn ((I.stp u a j).rep ((I.stp u a j).cl b d)) := by
  refine @normal_rep ((I.stp0 u a j).G b) ((I.stp0 u a j).D b) _ _ ((I.stp0 u a j).actD b) (fun q => cosetIn q) (I.pref u a j b)
      (fun q => ⟨fun hq => hq.2.1 hj, fun hq => ⟨fun h0 => by have := B.R.two_le_m; omega, fun _ => hq, fun h0 => by omega⟩⟩)
      d d' fun g => funext fun P => ?_
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · exact cosetIn_eq_of_mem hj (good_act hI ht hj b g d' hd' P hP) (good_act hI ht hj b g d hd P hP)
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
    have h1 := rep_mem hj d P
    exact cosetIn_eq_of_mem hj ((mem_act b g d' P hP hQ _).2 (h ▸ h1)) ((mem_act b g d P hP hQ _).2 h1)

variable {l : I.Laws} {Z : TC.Later B (I.cols l)} {Ch : ℕ → Type} {A : TwDat I l Z u a Ch}

/- English proof (translation)
Establish `hi : j ≤ B.R.m` using `by omega`. Take `⟨⟨b₁, c⟩, rfl⟩` from `hA.chOf_onto j hi β`. Take `⟨⟨b₂, c'⟩, rfl⟩` from `hA.chOf_onto j hi β'`. Take `rfl` from `idx_eq hI hj b b₁`. Take `rfl` from `idx_eq hI hj b b₂`.

Establish `h1` using `(hA.rep j hi ⟨b, c⟩).2`. Establish `h2` using `(hA.rep j hi ⟨b, c'⟩).2`. Unfold `Good at hβ hβ'`. Rewrite `hβ`, `h` using `[← h1]`. Rewrite `hβ'`, `h` using `[← h2]`.

Use `choose κ hκ z hz hz' using fun P : I.Q a => h ⟨P.1, Finset.mem_union_right _ P.2⟩ P.2`. Set `g : (I.stp u a j).G b` to `(1, 1, ⟨κ, fun P _ => hκ P⟩)`. Establish `hg` using `good_act hI ht hj b g _ hβ`. Establish `e` using `rep_congr hI ht hj b _ _ hg hβ' (funext fun P => by`. Distinguish the cases in `hP : P.1 ∈ (B.primes X).vGs`.

Conclude with `cosetIn_eq_of_mem hj (hg P hP) (hβ' P hP)`. Establish `hQ : P.1 ∈ I.Q a` using `(Finset.mem_union.mp P.2).resolve_left hP`. Conclude with `cosetIn_eq_of_mem hj ((mem_act b g _ P hP hQ _).2 (hz ⟨P.1, hQ⟩)) (hz' ⟨P.1, hQ⟩))`. Establish `e1 : (I.stp u a j).cl b ((I.stp u a j).act b g ((I.stp u a j).rep ⟨b, c⟩)) = ⟨b, c⟩` using `congrArg (Sigma.mk b) (Eq.trans (Quotient.sound (s := @MulAction.orbitRel _ _ _ ((I.stp u a j).actD b)) ⟨g, rfl⟩) ((I.stp u a j).rp_spec b c))`. Establish `e2 : (I.stp u a j).cl b ((I.stp u a j).rep ⟨b, c'⟩) = ⟨b, c'⟩` using `congrArg (Sigma.mk b) ((I.stp u a j).rp_spec b c')`.

Rewrite `e` using `[e1, e2]`. Conclude with `((hA.reads j hi).key _ _).2 ⟨rfl, e.symm⟩`.
-/
theorem chart_ext (hI : I.Ok) (ht : I.IsTw) (hA : A.Is) (hj : j + 1 = B.R.m) (b : Idx I.sel (I.tup a) (I.idx a) j) (β β' : Ch j)
    (hβ : Good (A.p0 j β)) (hβ' : Good (A.p0 j β'))
    (h : ∀ (P : rowSG (B.primes X) I.sel (I.tup a)) (hQ : P.1 ∈ I.Q a), ∃ κ ∈ (levQ I a j b ⟨P.1, hQ⟩).H,
      ∃ z ∈ cosetIn (A.p0 j β) P, κ.1 z ∈ cosetIn (A.p0 j β') P) : β = β' := by
  have hi : j ≤ B.R.m := by omega
  obtain ⟨⟨b₁, c⟩, rfl⟩ := hA.chOf_onto j hi β
  obtain ⟨⟨b₂, c'⟩, rfl⟩ := hA.chOf_onto j hi β'
  obtain rfl := idx_eq hI hj b b₁
  obtain rfl := idx_eq hI hj b b₂
  have h1 := (hA.rep j hi ⟨b, c⟩).2
  have h2 := (hA.rep j hi ⟨b, c'⟩).2
  unfold Good at hβ hβ'
  rw [← h1] at hβ h
  rw [← h2] at hβ' h
  choose κ hκ z hz hz' using fun P : I.Q a => h ⟨P.1, Finset.mem_union_right _ P.2⟩ P.2
  let g : (I.stp u a j).G b := (1, 1, ⟨κ, fun P _ => hκ P⟩)
  have hg := good_act hI ht hj b g _ hβ
  have e := rep_congr hI ht hj b _ _ hg hβ' (funext fun P => by
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · exact cosetIn_eq_of_mem hj (hg P hP) (hβ' P hP)
    · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
      exact cosetIn_eq_of_mem hj ((mem_act b g _ P hP hQ _).2 (hz ⟨P.1, hQ⟩)) (hz' ⟨P.1, hQ⟩))
  have e1 : (I.stp u a j).cl b ((I.stp u a j).act b g ((I.stp u a j).rep ⟨b, c⟩)) = ⟨b, c⟩ :=
    congrArg (Sigma.mk b) (Eq.trans (Quotient.sound (s := @MulAction.orbitRel _ _ _ ((I.stp u a j).actD b)) ⟨g, rfl⟩) ((I.stp u a j).rp_spec b c))
  have e2 : (I.stp u a j).cl b ((I.stp u a j).rep ⟨b, c'⟩) = ⟨b, c'⟩ := congrArg (Sigma.mk b) ((I.stp u a j).rp_spec b c')
  rw [e1, e2] at e
  exact ((hA.reads j hi).key _ _).2 ⟨rfl, e.symm⟩

/- English proof (translation)
Establish `hi : j ≤ B.R.m` using `by omega`. Establish `: NeZero (B.R.N j)` using `⟨(B.R.N_pos j).ne'⟩`. Take `⟨p, hp, hp'⟩` from `exists_pt (cst := I.cst a) (u := u) hj (DecoF.base _ _ _ _ _) z hz`. Take `⟨g, hg⟩` from `Quotient.exact ((I.stp u a j).rp_spec b (Quotient.mk _ p))`. Establish `hg' : (I.stp u a j).act b g p = (I.stp u a j).rep ((I.stp u a j).cl b p)` using `hg`.

Establish `h1` using `(hA.rep j hi ((I.stp u a j).cl b p)).2`. Rewrite `h1` using `[← hg']`. Use `⟨A.chOf j ((I.stp u a j).cl b p), ?_, fun P hQ => ?_⟩` and prove the remaining obligations. Unfold `Good`. Rewrite using `[← h1]`.

Conclude with `good_act hI ht hj b g p hp`. Establish `hP` using `Q_notMem_of_ok hI a _ hQ`. Rewrite using `[← h1]`. Conclude with `⟨g.2.2.1 ⟨P.1, hQ⟩, g.2.2.2 _ (Set.mem_univ _), (mem_act b g p P hP hQ _).2 (hp' P hP)⟩`.
-/
theorem exists_chart (hI : I.Ok) (ht : I.IsTw) (hA : A.Is) (hj : j + 1 = B.R.m) (b : Idx I.sel (I.tup a) (I.idx a) j)
    (z : rowSG (B.primes X) I.sel (I.tup a) → Sp B.fields.E (B.R.N j))
    (hz : ∀ P, P.1 ∉ (B.primes X).vGs → (qOf P.1 : B.fields.E) ^ (I.cst a).M • z P ∈ stdAt B.fields.E (B.R.N j) P.1) :
    ∃ β : Ch j, Good (A.p0 j β) ∧ ∀ (P : rowSG (B.primes X) I.sel (I.tup a)) (hQ : P.1 ∈ I.Q a),
      ∃ κ ∈ (levQ I a j b ⟨P.1, hQ⟩).H, κ.1 (z P) ∈ cosetIn (A.p0 j β) P := by
  have hi : j ≤ B.R.m := by omega
  have : NeZero (B.R.N j) := ⟨(B.R.N_pos j).ne'⟩
  obtain ⟨p, hp, hp'⟩ := exists_pt (cst := I.cst a) (u := u) hj (DecoF.base _ _ _ _ _) z hz
  obtain ⟨g, hg⟩ := Quotient.exact ((I.stp u a j).rp_spec b (Quotient.mk _ p))
  have hg' : (I.stp u a j).act b g p = (I.stp u a j).rep ((I.stp u a j).cl b p) := hg
  have h1 := (hA.rep j hi ((I.stp u a j).cl b p)).2
  rw [← hg'] at h1
  refine ⟨A.chOf j ((I.stp u a j).cl b p), ?_, fun P hQ => ?_⟩
  · unfold Good
    rw [← h1]
    exact good_act hI ht hj b g p hp
  · have hP := Q_notMem_of_ok hI a _ hQ
    rw [← h1]
    exact ⟨g.2.2.1 ⟨P.1, hQ⟩, g.2.2.2 _ (Set.mem_univ _), (mem_act b g p P hP hQ _).2 (hp' P hP)⟩

/- English proof (translation)
Establish `hh : ∀ (al : (I.idx a).β i) P, P.1 ∈ (B.primes X).vGs → (I.idx a).h i al P = 1`. Rewrite using `[(ht a).2]`. Conclude with `twSt_h_g _ _ _ _ _ i`. Establish `hx : xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) (A.p0 i α) (A.p0 (i + 1) γ) ≠ 0` using `fun e => hz (by unfold TwDat.xi; rw [e]; exact map_zero _)`. Conclude with `fun P hP => mem_cosetIn_of_res hi _ hP (degOne_of_ok hI a P).2 (Keep.res_of_xiAt hi (hI.sharp _) hh hx P hP)`.
-/
theorem good_of_xi (hI : I.Ok) (ht : I.IsTw) {i : ℕ} (hi : i + 1 + 1 = B.R.m) (h : i + 1 ≤ B.R.m) (α : Ch i) (γ : Ch (i + 1)) (z)
    (hz : A.xi i h α γ z ≠ 0) : Good (A.p0 (i + 1) γ) := by
  have hh : ∀ (al : (I.idx a).β i) P, P.1 ∈ (B.primes X).vGs → (I.idx a).h i al P = 1 := by
    rw [(ht a).2]
    exact twSt_h_g _ _ _ _ _ i
  have hx : xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) (A.p0 i α) (A.p0 (i + 1) γ) ≠ 0 := fun e =>
    hz (by unfold TwDat.xi; rw [e]; exact map_zero _)
  exact fun P hP => mem_cosetIn_of_res hi _ hP (degOne_of_ok hI a P).2 (Keep.res_of_xiAt hi (hI.sharp _) hh hx P hP)

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `hi : j ≤ B.R.m` using `by omega`. Establish `h0` using `rep_mem hj (A.p0 j β) P`. Establish `hv` using `(MemChart.kStd_spec l.pr u (B.R.N j)).2.1`. Rewrite `hv` using `[← hk]`. Distinguish the cases in `hP : P.1 ∈ (B.primes X).vGs`.

Use `swap`. Establish `e` using `GlobalTheory.QTw.frsF_base_eq_self A hA hI P hP j hi β hv`. Establish `e' : (frsF I.sel (I.tup a) (A.p0 j β).1.1 P).symm (repY (A.p0 j β).1.2) = repY (A.p0 j β).1.2`. Rewrite using `[LinearEquiv.symm_apply_eq, e]`. Rewrite `h0` using `[e']`. Then use the resulting hypothesis.

Establish `hT : ((B.T u : ℕ) : 𝓞 B.host.F) ∉ (P.1.under (𝓞 B.host.F)).asIdeal`. Introduce `hm`. Apply `GlobalTheory.KerT.T_notMem_rowSG (I.tup a) (GlobalTheory.BasePrimes.primes_ok B X).1 hI.sel_ok (hI.T_mem u) P.1 P.2` to reduce the goal to its premises. Use `Ideal.mem_comap.1 hm` as an intermediate fact. Simplify `this` using `[map_natCast]`.

Take `⟨hpt, hN⟩` from `hA.base j hi β`. Use `set f := frsF I.sel (I.tup a) (A.p0 j β).1.1 P with hf`. Establish `hl : TopStep.IsLiftFr (A.p0 j β).1.1.deco.1 ⟨P.1, hP⟩ f`. Rewrite using `[hf]`. Unfold `frsF`.

Rewrite using `[dif_pos hP]`. Conclude with `TopStep.liftFr_spec (A.p0 j β).1.1.deco.2 _`. Establish `hs : ∀ z, f z ∈ stdAt B.fields.E (B.R.N j) P.1 ↔ z ∈ stdAt B.fields.E (B.R.N j) P.1` using `fun z => by`. Use `hl.1 z` as an intermediate fact. Rewrite `this` using `[Deco.at, hN]`. Then use the resulting hypothesis.

Establish `hc` using `GlobalTheory.Transport.Pen.lift_cong hpt ⟨P.1, hP⟩ hl`. Establish `h1 : ColAd.locM P.1 (A.kb j β)⁻¹ = 1`. Use `Matrix.ext fun r s => ?_` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`. Conclude with `ZeroMove.adAt_entry_one P.1 (by rw [map_inv, hv _ hT, inv_one]) r s`.

Rewrite `hc` using `[h1, Matrix.one_mul]`. Establish `h2` using `ColAd.mem_prinCong_of_sm (c := 1) (⟨f, hs⟩ : GLint B.fields.E (B.R.N j) P.1) fun r s => by`. Unfold `ColAd.dep`. Rewrite using `[pow_one]`. Conclude with `GlobalTheory.Transport.Pen.val_le_q (degOne_of_ok hI a P).2 (hc r s)`.

Establish `hq0 : (qOf P.1 : B.fields.E) ≠ 0` using `GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1`. Take `⟨y, hy, hY⟩` from `(A.p0 j β).mem_ybSet hj`. Establish `h3` using `(A.p0 j β).repY_mem hj`. Use `set z := repY (A.p0 j β).1.2 with hz`. Rewrite `h3` using `[hY]`.

Establish `h4` using `(mem_locLat _ _ _ _).1 hy P`. Establish `h5` using `(mem_locLat _ _ _ _).1 h3 P`. Simplify using `only [if_pos hP, zpow_zero, inv_one, one_smul, _root_.zpow_neg_one, inv_inv, hN] at h4 h5`. Establish `h6 : (qOf P.1 : B.fields.E) • f.symm z ∈ stdAt B.fields.E (B.R.N j) P.1`. Rewrite using `[← hs, map_smul, LinearEquiv.apply_symm_apply, ← add_sub_cancel y z, smul_add]`.

Use `add_mem h4 ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `nsmul_mem h5 _`. Establish `h7` using `h2 _ h6`. Use `mem_of_sub h0 ?_` and prove the remaining obligations.

Rewrite using `[if_pos hP, pow_zero, inv_one, one_smul]`. Use `h7 using 1` and compare the differences between its conclusion and the goal. Use `show _ = _ • (f _ - _)`. Rewrite using `[map_smul, LinearEquiv.apply_symm_apply, ← smul_sub, pow_one, inv_smul_smul₀ hq0]`.
-/
theorem repY_mem (hI : I.Ok) (hA : A.Is) (hj : j + 1 = B.R.m) (β : Ch j) (hk : A.kb j β = TC.kStd X u (B.R.N j))
    (P : rowSG (B.primes X) I.sel (I.tup a)) : repY (A.p0 j β).1.2 ∈ cosetIn (A.p0 j β) P := by
  have hi : j ≤ B.R.m := by omega
  have h0 := rep_mem hj (A.p0 j β) P
  have hv := (MemChart.kStd_spec l.pr u (B.R.N j)).2.1
  rw [← hk] at hv
  by_cases hP : P.1 ∈ (B.primes X).vGs
  swap
  · have e := GlobalTheory.QTw.frsF_base_eq_self A hA hI P hP j hi β hv
    have e' : (frsF I.sel (I.tup a) (A.p0 j β).1.1 P).symm (repY (A.p0 j β).1.2) = repY (A.p0 j β).1.2 := by
      rw [LinearEquiv.symm_apply_eq, e]
    rwa [e'] at h0
  have hT : ((B.T u : ℕ) : 𝓞 B.host.F) ∉ (P.1.under (𝓞 B.host.F)).asIdeal := by
    intro hm
    apply GlobalTheory.KerT.T_notMem_rowSG (I.tup a) (GlobalTheory.BasePrimes.primes_ok B X).1 hI.sel_ok (hI.T_mem u) P.1 P.2
    have := Ideal.mem_comap.1 hm
    simpa [map_natCast] using this
  obtain ⟨hpt, hN⟩ := hA.base j hi β
  set f := frsF I.sel (I.tup a) (A.p0 j β).1.1 P with hf
  have hl : TopStep.IsLiftFr (A.p0 j β).1.1.deco.1 ⟨P.1, hP⟩ f := by
    rw [hf]
    unfold frsF
    rw [dif_pos hP]
    exact TopStep.liftFr_spec (A.p0 j β).1.1.deco.2 _
  have hs : ∀ z, f z ∈ stdAt B.fields.E (B.R.N j) P.1 ↔ z ∈ stdAt B.fields.E (B.R.N j) P.1 := fun z => by
    have := hl.1 z; rwa [Deco.at, hN] at this
  have hc := GlobalTheory.Transport.Pen.lift_cong hpt ⟨P.1, hP⟩ hl
  have h1 : ColAd.locM P.1 (A.kb j β)⁻¹ = 1 := by
    refine Matrix.ext fun r s => ?_
    rw [Matrix.one_apply]
    exact ZeroMove.adAt_entry_one P.1 (by rw [map_inv, hv _ hT, inv_one]) r s
  rw [h1, Matrix.one_mul] at hc
  have h2 := ColAd.mem_prinCong_of_sm (c := 1) (⟨f, hs⟩ : GLint B.fields.E (B.R.N j) P.1) fun r s => by
    unfold ColAd.dep
    rw [pow_one]
    exact GlobalTheory.Transport.Pen.val_le_q (degOne_of_ok hI a P).2 (hc r s)
  have hq0 : (qOf P.1 : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
  obtain ⟨y, hy, hY⟩ := (A.p0 j β).mem_ybSet hj
  have h3 := (A.p0 j β).repY_mem hj
  set z := repY (A.p0 j β).1.2 with hz
  rw [hY] at h3
  have h4 := (mem_locLat _ _ _ _).1 hy P
  have h5 := (mem_locLat _ _ _ _).1 h3 P
  simp only [if_pos hP, zpow_zero, inv_one, one_smul, _root_.zpow_neg_one, inv_inv, hN] at h4 h5
  have h6 : (qOf P.1 : B.fields.E) • f.symm z ∈ stdAt B.fields.E (B.R.N j) P.1 := by
    rw [← hs, map_smul, LinearEquiv.apply_symm_apply, ← add_sub_cancel y z, smul_add]
    refine add_mem h4 ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem h5 _
  have h7 := h2 _ h6
  refine mem_of_sub h0 ?_
  rw [if_pos hP, pow_zero, inv_one, one_smul]
  convert h7 using 1
  show _ = _ • (f _ - _)
  rw [map_smul, LinearEquiv.apply_symm_apply, ← smul_sub, pow_one, inv_smul_smul₀ hq0]

end True

end GlobalTheory.PenChart
