import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.IsLevelOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.SuperDiagUSingle

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Whittaker

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option linter.unusedSectionVars false

namespace WhittakerInverseTranspose

section Tilde

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem invT_invT' {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    GlobalTheory.CuspRep.invT n R (GlobalTheory.CuspRep.invT n R g) = g := Units.ext rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_invT' {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    ((GlobalTheory.CuspRep.invT n R g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ := rfl

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[GeneralLinearGroup.map_apply, val_invT', val_invT', ← map_inv, Matrix.transpose_apply, Matrix.transpose_apply, GeneralLinearGroup.map_apply]`.
-/
theorem invT_map' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (GlobalTheory.CuspRep.invT n R g) = GlobalTheory.CuspRep.invT n S (GeneralLinearGroup.map f g) := by
  ext i j
  rw [GeneralLinearGroup.map_apply, val_invT', val_invT', ← map_inv, Matrix.transpose_apply,
    Matrix.transpose_apply, GeneralLinearGroup.map_apply]

/- English proof (translation)
Take `⟨x, hx, rfl⟩` from `hg`. Use `⟨GlobalTheory.CuspRep.invT N _ x, ?_, invT_map' _ _ x⟩` and prove the remaining obligations. Establish `hx' : GeneralLinearGroup.map (IsLocalRing.residue _) x = 1` using `hx`. Use `show GeneralLinearGroup.map (IsLocalRing.residue _) (GlobalTheory.CuspRep.invT N _ x) = 1`. Rewrite using `[invT_map', hx', map_one]`.
-/
theorem invT_mem_KOne {N : ℕ} {g : GL (Fin N) k} (hg : g ∈ KOne k (Fin N)) :
    GlobalTheory.CuspRep.invT N k g ∈ KOne k (Fin N) := by
  obtain ⟨x, hx, rfl⟩ := hg
  refine ⟨GlobalTheory.CuspRep.invT N _ x, ?_, invT_map' _ _ x⟩
  have hx' : GeneralLinearGroup.map (IsLocalRing.residue _) x = 1 := hx
  show GeneralLinearGroup.map (IsLocalRing.residue _) (GlobalTheory.CuspRep.invT N _ x) = 1
  rw [invT_map', hx', map_one]

/- English proof (translation)
The claim follows from `Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩`.
-/
theorem continuous_invT' (N : ℕ) : Continuous (GlobalTheory.CuspRep.invT N k) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Introduce `v` and use `(h v).preimage (continuous_invT' N)`.
-/
theorem isSmooth_comp_invT {N : ℕ} {ρ : Representation ℂ (GL (Fin N) k) V} (h : IsSmooth ρ) :
    IsSmooth (ρ.comp (GlobalTheory.CuspRep.invT N k)) :=
  fun v => (h v).preimage (continuous_invT' N)

/- English proof (translation)
Set `Φ : Subrepresentation (ρ.comp (GlobalTheory.CuspRep.invT N k)) ≃o Subrepresentation ρ` to `{ toFun := fun U => ⟨U.toSubmodule, fun g v hv => by`. Rewrite using `[← invT_invT' N g]`. Conclude with `U.apply_mem_toSubmodule (GlobalTheory.CuspRep.invT N k g) hv⟩`. Use `invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule _ hv⟩`. Use `left_inv := fun _ => rfl`.

Use `right_inv := fun _ => rfl`. Use the proof step `map_rel_iff' := Iff.rfl }`. Establish `: IsSimpleOrder (Subrepresentation ρ)` using `h`. Conclude with `Φ.isSimpleOrder`.
-/
theorem isIrreducible_comp_invT {N : ℕ} {ρ : Representation ℂ (GL (Fin N) k) V} (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp (GlobalTheory.CuspRep.invT N k)) := by
  let Φ : Subrepresentation (ρ.comp (GlobalTheory.CuspRep.invT N k)) ≃o Subrepresentation ρ :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        rw [← invT_invT' N g]
        exact U.apply_mem_toSubmodule (GlobalTheory.CuspRep.invT N k g) hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule _ hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have : IsSimpleOrder (Subrepresentation ρ) := h
  exact Φ.isSimpleOrder

/- English proof (translation)
Rewrite using `[mem_unipRad, mem_parab_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ x y`. Take `⟨⟨a, i⟩, rfl⟩` from `e.surjective x`. Take `⟨⟨b, j⟩, rfl⟩` from `e.surjective y`.

Simplify using `only [Equiv.symm_apply_apply]`. Use `⟨fun hab => h1 a b i j hab, fun hab => ?_⟩` and prove the remaining obligations. Substitute `hab` using the available equality. Rewrite using `[h2 a i j]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne hij, Matrix.one_apply_ne]`. Introduce `h`. Conclude with `hij (eq_of_heq (Sigma.mk.inj_iff.1 (e.injective h)).2)`.

Introduce `h`. Use `⟨fun a b i j hab => (h _ _).1 (by simpa using hab), fun a i j => ?_⟩` and prove the remaining obligations. Rewrite using `[(h _ _).2 (by simp)]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne hij, Matrix.one_apply_ne]`. Introduce `h'`. Conclude with `hij (eq_of_heq (Sigma.mk.inj_iff.1 (e.injective h')).2)`.
-/
theorem mem_unipRad_iff' {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N) (g : GL (Fin N) k) :
    g ∈ unipRad k e ↔ ∀ x y, ((e.symm y).1 < (e.symm x).1 → (g : Matrix (Fin N) (Fin N) k) x y = 0) ∧
      ((e.symm x).1 = (e.symm y).1 →
        (g : Matrix (Fin N) (Fin N) k) x y = (1 : Matrix (Fin N) (Fin N) k) x y) := by
  rw [mem_unipRad, mem_parab_iff]
  constructor
  · rintro ⟨h1, h2⟩ x y
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
    simp only [Equiv.symm_apply_apply]
    refine ⟨fun hab => h1 a b i j hab, fun hab => ?_⟩
    subst hab
    rw [h2 a i j]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne]
      intro h; exact hij (eq_of_heq (Sigma.mk.inj_iff.1 (e.injective h)).2)
  · intro h
    refine ⟨fun a b i j hab => (h _ _).1 (by simpa using hab), fun a i j => ?_⟩
    rw [(h _ _).2 (by simp)]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne]
      intro h'; exact hij (eq_of_heq (Sigma.mk.inj_iff.1 (e.injective h')).2)

/- English proof (translation)
Establish `hi` using `(mem_unipRad_iff' e _).1 (inv_mem hg)`. Use `(mem_unipRad_iff' e' _).2 fun x y => ⟨fun hxy => ?_, fun hxy => ?_⟩` and prove the remaining obligations. Rewrite using `[val_invT', Matrix.transpose_apply]`. Use `(hi y x).1 ?_` and prove the remaining obligations. Rewrite `hxy` using `[he, he]`.

Conclude with `Fin.rev_lt_rev.1 hxy`. Rewrite using `[val_invT', Matrix.transpose_apply, (hi y x).2 ?_]`. Distinguish the cases in `hxy' : x = y`. Substitute `hxy'` using the available equality. Both sides reduce to the same expression.

Rewrite using `[Matrix.one_apply_ne hxy', Matrix.one_apply_ne (Ne.symm hxy')]`. Rewrite `hxy` using `[he, he]`. Conclude with `(Fin.rev_injective hxy).symm`.
-/
theorem invT_mem_unipRad {s N : ℕ} {d d' : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N)
    (e' : (Σ a, Fin (d' a)) ≃ Fin N) (he : ∀ x, (e'.symm x).1 = Fin.rev (e.symm x).1) {g : GL (Fin N) k}
    (hg : g ∈ unipRad k e) : GlobalTheory.CuspRep.invT N k g ∈ unipRad k e' := by
  have hi := (mem_unipRad_iff' e _).1 (inv_mem hg)
  refine (mem_unipRad_iff' e' _).2 fun x y => ⟨fun hxy => ?_, fun hxy => ?_⟩
  · rw [val_invT', Matrix.transpose_apply]
    refine (hi y x).1 ?_
    rw [he, he] at hxy
    exact Fin.rev_lt_rev.1 hxy
  · rw [val_invT', Matrix.transpose_apply, (hi y x).2 ?_]
    · by_cases hxy' : x = y
      · subst hxy'; rfl
      · rw [Matrix.one_apply_ne hxy', Matrix.one_apply_ne (Ne.symm hxy')]
    · rw [he, he] at hxy; exact (Fin.rev_injective hxy).symm

/- English proof (translation)
Use `⟨isSmooth_comp_invT h.1, fun s d e hne => ?_⟩` and prove the remaining obligations. Set `e' : (Σ a, Fin (d (Fin.revPerm a))) ≃ Fin N` to `(Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm).trans e`. Establish `he : ∀ x, (e'.symm x).1 = Fin.rev (e.symm x).1` using `fun x => by`. Establish `h1 : e'.symm x = (Equiv.sigmaCongrLeft (β` using `fun a => Fin (d a)) Fin.revPerm).symm (e.symm x) := rfl`. Take `⟨⟨a, i⟩, hq⟩ : ∃ q, (Equiv.sigmaCongrLeft (β` from `fun a => Fin (d a)) Fin.revPerm).symm (e.symm x) = q := ⟨_, rfl⟩`.

Establish `h2` using `congrArg (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm) hq`. Rewrite `h2` using `[Equiv.apply_symm_apply, Equiv.sigmaCongrLeft_apply]`. Rewrite using `[h1, hq, h2]`. Simplify using the standard rewrite rules. Establish `he' : ∀ x, (e.symm x).1 = Fin.rev (e'.symm x).1` using `fun x => by rw [he, Fin.rev_rev]`.

Establish `hne' : unipRad k e' ≠ ⊥`. Take `⟨⟨g, hg⟩, hg1⟩` from `Subgroup.ne_bot_iff_exists_ne_one.1 hne`. Use `Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨_, invT_mem_unipRad e e' he hg⟩, fun h1 => hg1 ?_⟩` and prove the remaining obligations. Establish `h2 : GlobalTheory.CuspRep.invT N k g = 1` using `congrArg Subtype.val h1`. Use `Subtype.ext ?_` and prove the remaining obligations.

Use `show g = 1`. Rewrite using `[← invT_invT' N g, h2, map_one]`. Establish `hs` using `h.2 s (fun a => d (Fin.revPerm a)) e' hne'`. Establish `htop : twKer ρ (unipRad k e') 1 = ⊤` using `Submodule.Quotient.subsingleton_iff.1 hs`. Use `show Subsingleton (V ⧸ twKer _ _ 1)`.

Rewrite using `[Submodule.Quotient.subsingleton_iff, eq_top_iff, ← htop]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, v, rfl⟩`. Use `Submodule.subset_span ⟨⟨GlobalTheory.CuspRep.invT N k n, invT_mem_unipRad e' e he' n.2⟩, v, ?_⟩` and prove the remaining obligations. Simplify using `[invT_invT']`.
-/
theorem isCuspidal_comp_invT {N : ℕ} {ρ : Representation ℂ (GL (Fin N) k) V} (h : IsCuspidal ρ) :
    IsCuspidal (ρ.comp (GlobalTheory.CuspRep.invT N k)) := by
  refine ⟨isSmooth_comp_invT h.1, fun s d e hne => ?_⟩
  let e' : (Σ a, Fin (d (Fin.revPerm a))) ≃ Fin N :=
    (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm).trans e
  have he : ∀ x, (e'.symm x).1 = Fin.rev (e.symm x).1 := fun x => by
    have h1 : e'.symm x = (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm).symm (e.symm x) := rfl
    obtain ⟨⟨a, i⟩, hq⟩ : ∃ q, (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm).symm (e.symm x) = q :=
      ⟨_, rfl⟩
    have h2 := congrArg (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm) hq
    rw [Equiv.apply_symm_apply, Equiv.sigmaCongrLeft_apply] at h2
    rw [h1, hq, h2]
    simp
  have he' : ∀ x, (e.symm x).1 = Fin.rev (e'.symm x).1 := fun x => by rw [he, Fin.rev_rev]
  have hne' : unipRad k e' ≠ ⊥ := by
    obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨_, invT_mem_unipRad e e' he hg⟩, fun h1 => hg1 ?_⟩
    have h2 : GlobalTheory.CuspRep.invT N k g = 1 := congrArg Subtype.val h1
    refine Subtype.ext ?_
    show g = 1
    rw [← invT_invT' N g, h2, map_one]
  have hs := h.2 s (fun a => d (Fin.revPerm a)) e' hne'
  have htop : twKer ρ (unipRad k e') 1 = ⊤ := Submodule.Quotient.subsingleton_iff.1 hs
  show Subsingleton (V ⧸ twKer _ _ 1)
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff, ← htop]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, v, rfl⟩
  refine Submodule.subset_span ⟨⟨GlobalTheory.CuspRep.invT N k n, invT_mem_unipRad e' e he' n.2⟩, v, ?_⟩
  simp [invT_invT']

/- English proof (translation)
Simplify using `only [superDiag, Finset.sum_filter, Fintype.sum_prod_type]`.
-/
theorem superDiag_pairs' {N : ℕ} (g : GL (Fin N) k) :
    superDiag g = ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1, g.val p.1 p.2 := by
  simp only [superDiag, Finset.sum_filter, Fintype.sum_prod_type]

/- English proof (translation)
Rewrite using `[superDiag_pairs']`. Both sides reduce to the same expression.
-/
theorem val_whitChar' (ψ : AddChar k Circle) {N : ℕ} (u : unipB k (Fin N)) :
    ((GlobalTheory.LocGL.whitChar ψ N u : ℂˣ) : ℂ) = ψ (superDiag u.1) := by
  rw [superDiag_pairs']; rfl

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single j.rev]`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i.rev]`. Simplify using `[longElt]`. Introduce `b _ hb`. Simplify using `[longElt, hb]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Establish `: ¬ j = b.rev` using `fun h => hb (by rw [h, Fin.rev_rev])`. Simplify using `[longElt, this]`. Simplify using the standard rewrite rules.
-/
theorem longElt_conj_apply {N : ℕ} (M : Matrix (Fin N) (Fin N) k) (i j : Fin N) :
    ((longElt N k : Matrix (Fin N) (Fin N) k) * M * (longElt N k : Matrix (Fin N) (Fin N) k)) i j =
      M i.rev j.rev := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j.rev]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
    · simp [longElt]
    · intro b _ hb; simp [longElt, hb]
    · simp
  · intro b _ hb
    have : ¬ j = b.rev := fun h => hb (by rw [h, Fin.rev_rev])
    simp [longElt, this]
  · simp

/- English proof (translation)
Introduce `u hu x`. Establish `hw : longElt N k * longElt N k = 1` using `Units.ext (antidiag_mul_self N k)`. Establish `hent : ∀ i j, ((longElt N k * GlobalTheory.CuspRep.invT N k u * longElt N k : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = ((u⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) j.rev i.rev`. Introduce `i j`. Rewrite using `[Units.val_mul, Units.val_mul, longElt_conj_apply, val_invT', Matrix.transpose_apply]`.

Establish `hu'` using `((mem_unipB k).1 (inv_mem hu))`. Establish `hc : longElt N k * GlobalTheory.CuspRep.invT N k u * longElt N k ∈ unipB k (Fin N)` using `(mem_unipB k).2 ⟨fun i j hji => by rw [hent]; exact hu'.1 _ _ (Fin.rev_lt_rev.2 hji), fun i => by rw [hent]; exact hu'.2 _⟩`. Establish `hsd : superDiag (longElt N k * GlobalTheory.CuspRep.invT N k u * longElt N k) = superDiag u⁻¹`. Rewrite using `[superDiag_pairs', superDiag_pairs']`. Use `Finset.sum_nbij' (fun p => (p.2.rev, p.1.rev)) (fun p => (p.2.rev, p.1.rev)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at hp ⊢`. Use `p.1.isLt` as an intermediate fact. Use `p.2.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at hp ⊢`. Use `p.1.isLt` as an intermediate fact. Use `p.2.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Introduce `p _`. Simplify using the standard rewrite rules. Introduce `p _`. Simplify using the standard rewrite rules. Introduce `p _`.

Conclude with `hent p.1 p.2`. Establish `e1 : ρ (longElt N k) (ρ (GlobalTheory.CuspRep.invT N k u) x) = ρ (longElt N k * GlobalTheory.CuspRep.invT N k u * longElt N k) (ρ (longElt N k) x)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul]`. Both sides reduce to the same expression.

Use `_ = ρ (longElt N k * GlobalTheory.CuspRep.invT N k u * longElt N k * longElt N k) x := by`. Rewrite using `[mul_assoc (longElt N k * GlobalTheory.CuspRep.invT N k u), hw, mul_one]`. Use `_ = _ := by rw [map_mul]; rfl`. Establish `hψ : (ψ (superDiag u⁻¹) : ℂ) = ((ψ⁻¹ (superDiag u) : Circle) : ℂ)`. Establish `h3` using `congrArg Units.val (map_inv (GlobalTheory.LocGL.whitChar ψ N) ⟨u, hu⟩)`.

Rewrite `h3` using `[val_whitChar', Units.val_inv_eq_inv_val, val_whitChar']`. Rewrite using `[show (u⁻¹ : GL (Fin N) k) = ((⟨u, hu⟩⁻¹ : unipB k (Fin N)) : GL (Fin N) k) from rfl, h3]`. Simplify using `[AddChar.map_neg_eq_inv]`. Simplify using `only [LinearMap.comp_apply, MonoidHom.comp_apply]`. Rewrite using `[e1, hl _ hc, hsd, hψ]`.
-/
theorem isFunctional_comp_invT {N : ℕ} (ψ : AddChar k Circle) (ρ : Representation ℂ (GL (Fin N) k) V)
    (l : Module.Dual ℂ V) (hl : IsFunctional ψ ρ l) :
    IsFunctional ψ⁻¹ (ρ.comp (GlobalTheory.CuspRep.invT N k)) (l ∘ₗ ρ (longElt N k)) := by
  intro u hu x
  have hw : longElt N k * longElt N k = 1 := Units.ext (antidiag_mul_self N k)
  have hent : ∀ i j, ((longElt N k * GlobalTheory.CuspRep.invT N k u * longElt N k : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) i j = ((u⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) j.rev i.rev := by
    intro i j
    rw [Units.val_mul, Units.val_mul, longElt_conj_apply, val_invT', Matrix.transpose_apply]
  have hu' := ((mem_unipB k).1 (inv_mem hu))
  have hc : longElt N k * GlobalTheory.CuspRep.invT N k u * longElt N k ∈ unipB k (Fin N) :=
    (mem_unipB k).2 ⟨fun i j hji => by rw [hent]; exact hu'.1 _ _ (Fin.rev_lt_rev.2 hji),
      fun i => by rw [hent]; exact hu'.2 _⟩
  have hsd : superDiag (longElt N k * GlobalTheory.CuspRep.invT N k u * longElt N k) = superDiag u⁻¹ := by
    rw [superDiag_pairs', superDiag_pairs']
    refine Finset.sum_nbij' (fun p => (p.2.rev, p.1.rev)) (fun p => (p.2.rev, p.1.rev)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at hp ⊢
      have := p.1.isLt; have := p.2.isLt; omega
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at hp ⊢
      have := p.1.isLt; have := p.2.isLt; omega
    · intro p _; simp
    · intro p _; simp
    · intro p _; exact hent p.1 p.2
  have e1 : ρ (longElt N k) (ρ (GlobalTheory.CuspRep.invT N k u) x) =
      ρ (longElt N k * GlobalTheory.CuspRep.invT N k u * longElt N k) (ρ (longElt N k) x) := by
    calc ρ (longElt N k) (ρ (GlobalTheory.CuspRep.invT N k u) x) = ρ (longElt N k * GlobalTheory.CuspRep.invT N k u) x := by
          rw [map_mul]; rfl
      _ = ρ (longElt N k * GlobalTheory.CuspRep.invT N k u * longElt N k * longElt N k) x := by
          rw [mul_assoc (longElt N k * GlobalTheory.CuspRep.invT N k u), hw, mul_one]
      _ = _ := by rw [map_mul]; rfl
  have hψ : (ψ (superDiag u⁻¹) : ℂ) = ((ψ⁻¹ (superDiag u) : Circle) : ℂ) := by
    have h3 := congrArg Units.val (map_inv (GlobalTheory.LocGL.whitChar ψ N) ⟨u, hu⟩)
    rw [val_whitChar', Units.val_inv_eq_inv_val, val_whitChar'] at h3
    rw [show (u⁻¹ : GL (Fin N) k) = ((⟨u, hu⟩⁻¹ : unipB k (Fin N)) : GL (Fin N) k) from rfl, h3]
    simp [AddChar.map_neg_eq_inv]
  simp only [LinearMap.comp_apply, MonoidHom.comp_apply]
  rw [e1, hl _ hc, hsd, hψ]

/- English proof (translation)
Take `⟨c, hc, hc1⟩` from `h`. Use `⟨c, fun x => ?_, hc1⟩` and prove the remaining obligations. Rewrite using `[← hc x]`. Simplify using `only [AddChar.inv_apply', inv_eq_one]`.
-/
theorem isLevelOne_inv {ψ : AddChar k Circle} (h : IsLevelOne ψ) : IsLevelOne ψ⁻¹ := by
  obtain ⟨c, hc, hc1⟩ := h
  refine ⟨c, fun x => ?_, hc1⟩
  rw [← hc x]
  simp only [AddChar.inv_apply', inv_eq_one]

/- English proof (translation)
Introduce `g` and use `hv ⟨_, invT_mem_KOne g.2⟩`.
-/
theorem mem_fixed_comp_invT {N : ℕ} {ρ : Representation ℂ (GL (Fin N) k) V} {v : V}
    (hv : v ∈ fixed ρ (KOne k (Fin N))) : v ∈ fixed (ρ.comp (GlobalTheory.CuspRep.invT N k)) (KOne k (Fin N)) :=
  fun g => hv ⟨_, invT_mem_KOne g.2⟩

def compInvT {n : ℕ} (π : IrrRep (GL (Fin n) k)) : IrrRep (GL (Fin n) k) where
  V := π.V
  ρ := π.ρ.comp (GlobalTheory.CuspRep.invT n k)
  smooth := isSmooth_comp_invT π.smooth
  irr := isIrreducible_comp_invT π.irr

/- English proof (translation)
Use `hA1 (compInvT π) (isCuspidal_comp_invT hπ) ψ⁻¹ (isLevelOne_inv hψ) (l ∘ₗ π.ρ (longElt (m + 1) k)) (isFunctional_comp_invT ψ π.ρ l hl) v (mem_fixed_comp_invT hv) g ?_` and prove the remaining obligations. Use `show l (π.ρ (longElt (m + 1) k) (π.ρ (GlobalTheory.CuspRep.invT (m + 1) k (corner g)) v)) ≠ 0`. Rewrite `hg` using `[tilde, map_mul]`. Then use the resulting hypothesis.
-/
theorem whittaker_support_tilde_of {m : ℕ}
    (hA1 : ∀ (π : IrrRep (GL (Fin (m + 1)) k)), IsCuspidal π.ρ → ∀ (ψ : AddChar k Circle), IsLevelOne ψ →
      ∀ (l : Module.Dual ℂ π.V), IsFunctional ψ π.ρ l → ∀ v ∈ fixed π.ρ (KOne k (Fin (m + 1))),
        ∀ g : GL (Fin m) k, l (π.ρ (corner g) v) ≠ 0 → valuation k ((GeneralLinearGroup.det g : kˣ) : k) = 1)
    (π : IrrRep (GL (Fin (m + 1)) k)) (hπ : IsCuspidal π.ρ)
    (ψ : AddChar k Circle) (hψ : IsLevelOne ψ) (l : Module.Dual ℂ π.V) (hl : IsFunctional ψ π.ρ l)
    (v : π.V) (hv : v ∈ fixed π.ρ (KOne k (Fin (m + 1)))) (g : GL (Fin m) k)
    (hg : l (π.ρ (tilde (corner g)) v) ≠ 0) : valuation k ((GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  refine hA1 (compInvT π) (isCuspidal_comp_invT hπ) ψ⁻¹ (isLevelOne_inv hψ) (l ∘ₗ π.ρ (longElt (m + 1) k))
    (isFunctional_comp_invT ψ π.ρ l hl) v (mem_fixed_comp_invT hv) g ?_
  show l (π.ρ (longElt (m + 1) k) (π.ρ (GlobalTheory.CuspRep.invT (m + 1) k (corner g)) v)) ≠ 0
  rwa [tilde, map_mul] at hg

end Tilde

end WhittakerInverseTranspose

/- English proof (translation)
The claim follows from `WhittakerInverseTranspose.whittaker_support_tilde_of (fun π hπ ψ hψ l hl v hv g hg => whittaker_support π hπ ψ hψ l hl v hv g hg) π hπ ψ hψ l hl v hv g hg`.
-/
theorem whittaker_support_tilde {m : ℕ} (π : IrrRep (GL (Fin (m + 1)) k)) (hπ : IsCuspidal π.ρ)
    (ψ : AddChar k Circle) (hψ : IsLevelOne ψ) (l : Module.Dual ℂ π.V) (hl : IsFunctional ψ π.ρ l)
    (v : π.V) (hv : v ∈ fixed π.ρ (KOne k (Fin (m + 1)))) (g : GL (Fin m) k)
    (hg : l (π.ρ (tilde (corner g)) v) ≠ 0) : valuation k ((GeneralLinearGroup.det g : kˣ) : k) = 1 :=
  WhittakerInverseTranspose.whittaker_support_tilde_of (fun π hπ ψ hψ l hl v hv g hg => whittaker_support π hπ ψ hψ l hl v hv g hg)
    π hπ ψ hψ l hl v hv g hg

end PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

end
