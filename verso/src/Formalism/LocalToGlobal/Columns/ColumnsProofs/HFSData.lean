import Mathlib
import Formalism.LocalToGlobal.Columns.RowForms
import Formalism.LocalToGlobal.Divisibility.TuplesLemmas
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

section TupMap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {K L : Type} [Field K] [Field L]
  (ι : K →+* L)

def chrMap : Chr F E K →* Chr F E L where
  toFun ξ := (Units.map ι.toMonoidHom).comp ξ
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chrMap_apply (ξ : Chr F E K) (x : (AfE F E)ˣ) : chrMap ι ξ x = Units.map ι.toMonoidHom (ξ x) := rfl

/- English proof (translation)
Introduce `a b h`. Use `first`. Consider the case `exact Units.ext (ι.injective (congrArg Units.val h))`. Consider the case `(apply Units.ext; apply ι.injective; have h' := congrArg Units.val h; simpa using h')`.
-/
theorem units_map_injective : Function.Injective (Units.map ι.toMonoidHom) := by
  intro a b h
  first
  | exact Units.ext (ι.injective (congrArg Units.val h))
  | (apply Units.ext; apply ι.injective; have h' := congrArg Units.val h; simpa using h')

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.mem_ker, chrMap_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `units_map_injective ι` to reduce the goal to its premises.

Rewrite using `[h, map_one]`. Introduce `h`. Rewrite using `[h, map_one]`.
-/
theorem chrMap_ker (ξ : Chr F E K) : (chrMap ι ξ).ker = ξ.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, chrMap_apply]
  constructor
  · intro h
    apply units_map_injective ι
    rw [h, map_one]
  · intro h
    rw [h, map_one]

/- English proof (translation)
Introduce `a b h`. Use `MonoidHom.ext fun x => units_map_injective ι ?_` and prove the remaining obligations. Establish `hx` using `DFunLike.congr_fun h x`. Rewrite `hx` using `[chrMap_apply, chrMap_apply]`. Then use the resulting hypothesis.
-/
theorem chrMap_injective : Function.Injective (chrMap (F := F) (E := E) ι) := by
  intro a b h
  refine MonoidHom.ext fun x => units_map_injective ι ?_
  have hx := DFunLike.congr_fun h x
  rwa [chrMap_apply, chrMap_apply] at hx

/- English proof (translation)
Establish `hk : (chrMap ι ξ).ker = ξ.ker` using `chrMap_ker ι ξ`. Establish `mk : ∀ (H : Subgroup (AfE F E)ˣ) (ζ : Chr F E L), ζ ∈ kills Lˣ H ↔ H ≤ ζ.ker` using `fun _ _ => Iff.rfl`. Establish `mk' : ∀ (H : Subgroup (AfE F E)ˣ) (ζ : Chr F E K), ζ ∈ kills Kˣ H ↔ H ≤ ζ.ker` using `fun _ _ => Iff.rfl`. Establish `mo : ∀ ζ : Chr F E L, ζ ∈ openChr F E L ↔ ∃ N : ℕ, 0 < N ∧ congN F E N ≤ ζ.ker` using `fun _ => Iff.rfl`. Establish `mo' : ∀ ζ : Chr F E K, ζ ∈ openChr F E K ↔ ∃ N : ℕ, 0 < N ∧ congN F E N ≤ ζ.ker` using `fun _ => Iff.rfl`.

Establish `hT : ∀ ζ : Chr F E K, IsOfFinOrder ζ → IsOfFinOrder (chrMap ι ζ)` using `fun ζ hζ => by first`. Consider the case `exact hζ.map (chrMap ι)`. Consider the case `exact (chrMap ι).isOfFinOrder hζ`. Consider the case `exact hζ.map`. Simplify using `only [tupGrp, finChar, Subgroup.mem_inf, Subgroup.mem_iInf, mk, mk', mo, mo', CommGroup.mem_torsion, hk] at h ⊢`.

Use `first`. Consider the case `exact ⟨⟨⟨⟨h.1.1.1.1, hT _ h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩`. Consider the case `exact ⟨⟨⟨⟨⟨h.1.1.1.1.1, h.1.1.1.1.2⟩, hT _ h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩`. Consider the case `(have hT' := hT _ h.1.1.1.2; tauto)`.
-/
theorem chrMap_mem_tupGrp {S : Set ℕ} {ξ : Chr F E K} (h : ξ ∈ tupGrp F E K S) : chrMap ι ξ ∈ tupGrp F E L S := by
  have hk : (chrMap ι ξ).ker = ξ.ker := chrMap_ker ι ξ
  have mk : ∀ (H : Subgroup (AfE F E)ˣ) (ζ : Chr F E L), ζ ∈ kills Lˣ H ↔ H ≤ ζ.ker := fun _ _ => Iff.rfl
  have mk' : ∀ (H : Subgroup (AfE F E)ˣ) (ζ : Chr F E K), ζ ∈ kills Kˣ H ↔ H ≤ ζ.ker := fun _ _ => Iff.rfl
  have mo : ∀ ζ : Chr F E L, ζ ∈ openChr F E L ↔ ∃ N : ℕ, 0 < N ∧ congN F E N ≤ ζ.ker := fun _ => Iff.rfl
  have mo' : ∀ ζ : Chr F E K, ζ ∈ openChr F E K ↔ ∃ N : ℕ, 0 < N ∧ congN F E N ≤ ζ.ker := fun _ => Iff.rfl
  have hT : ∀ ζ : Chr F E K, IsOfFinOrder ζ → IsOfFinOrder (chrMap ι ζ) := fun ζ hζ => by
    first
    | exact hζ.map (chrMap ι)
    | exact (chrMap ι).isOfFinOrder hζ
    | exact hζ.map
  simp only [tupGrp, finChar, Subgroup.mem_inf, Subgroup.mem_iInf, mk, mk', mo, mo', CommGroup.mem_torsion, hk] at h ⊢
  first
  | exact ⟨⟨⟨⟨h.1.1.1.1, hT _ h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩
  | exact ⟨⟨⟨⟨⟨h.1.1.1.1.1, h.1.1.1.1.2⟩, hT _ h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩
  | (have hT' := hT _ h.1.1.1.2; tauto)

def tupMap (S : Set ℕ) : Tup F E K S →* Tup F E L S :=
  ((chrMap ι).comp (tupGrp F E K S).subtype).codRestrict (tupGrp F E L S) fun x => chrMap_mem_tupGrp ι x.2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tupMap_coe {S : Set ℕ} (μ : Tup F E K S) : ((tupMap ι S μ : Tup F E L S) : Chr F E L) = chrMap ι μ := rfl

/- English proof (translation)
Introduce `a b h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `chrMap_injective ι` to reduce the goal to its premises. Use `first`. Consider the case `exact congrArg Subtype.val h`.

Consider the case `rw [← tupMap_coe, ← tupMap_coe, h]`.
-/
theorem tupMap_injective (S : Set ℕ) : Function.Injective (tupMap (F := F) (E := E) ι S) := by
  intro a b h
  apply Subtype.ext
  apply chrMap_injective ι
  first
  | exact congrArg Subtype.val h
  | rw [← tupMap_coe, ← tupMap_coe, h]

def tupMapEmb (S : Set ℕ) : Tup F E K S ↪ Tup F E L S := ⟨tupMap ι S, tupMap_injective ι S⟩

/- English proof (translation)
Use `first`. Consider the case `(unfold mu0; exact map_one _)`. Consider the case `simp [mu0]`.
-/
theorem tupleMap_trivialTuple (S : Set ℕ) : tupMap ι S (mu0 F E K S) = mu0 F E L S := by
  first
  | (unfold mu0; exact map_one _)
  | simp [mu0]

/- English proof (translation)
Use `first`. Consider the case `(unfold Qprime; rw [chrMap_ker])`. Consider the case `simp only [Qprime, chrMap_ker]`.
-/
theorem Qprime_chrMap (ξ : Chr F E K) : Qprime (chrMap ι ξ) = Qprime ξ := by
  first
  | (unfold Qprime; rw [chrMap_ker])
  | simp only [Qprime, chrMap_ker]

/- English proof (translation)
Unfold `IsResChar at h ⊢`. Introduce `v hv u a b hb hu hd hP`. Rewrite using `[chrMap_apply, h v hv u a b hb hu hd hP, MonoidHom.comp_apply]`.
-/
theorem isResChar_chrMap {ξ : Chr F E K} {P : HeightOneSpectrum (𝓞 E)} {χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ}
    (h : IsResChar ξ P χ) : IsResChar (chrMap ι ξ) P ((Units.map ι.toMonoidHom).comp χ) := by
  unfold IsResChar at h ⊢
  intro v hv u a b hb hu hd hP
  rw [chrMap_apply, h v hv u a b hb hu hd hP, MonoidHom.comp_apply]

/- English proof (translation)
Establish `hex` using `residue_character_exists F E K ξ ht P`. Establish `ht' : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ (chrMap ι ξ).ker`. Introduce `v`. Rewrite using `[chrMap_ker]`. Conclude with `ht v`.

Establish `hex'` using `residue_character_exists F E L (chrMap ι ξ) ht' P`. Establish `h1 : IsResChar ξ P (resChar ξ P)`. Unfold `resChar`. Rewrite using `[dif_pos hex.exists]`. Conclude with `hex.exists.choose_spec`.

Establish `h2 : IsResChar (chrMap ι ξ) P (resChar (chrMap ι ξ) P)`. Unfold `resChar`. Rewrite using `[dif_pos hex'.exists]`. Conclude with `hex'.exists.choose_spec`. Conclude with `hex'.unique h2 (isResChar_chrMap ι h1)`.
-/
theorem resChar_chrMap (ξ : Chr F E K) (ht : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker)
    (P : HeightOneSpectrum (𝓞 E)) : resChar (chrMap ι ξ) P = (Units.map ι.toMonoidHom).comp (resChar ξ P) := by
  have hex := residue_character_exists F E K ξ ht P
  have ht' : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ (chrMap ι ξ).ker := by
    intro v
    rw [chrMap_ker]
    exact ht v
  have hex' := residue_character_exists F E L (chrMap ι ξ) ht' P
  have h1 : IsResChar ξ P (resChar ξ P) := by
    unfold resChar
    rw [dif_pos hex.exists]
    exact hex.exists.choose_spec
  have h2 : IsResChar (chrMap ι ξ) P (resChar (chrMap ι ξ) P) := by
    unfold resChar
    rw [dif_pos hex'.exists]
    exact hex'.exists.choose_spec
  exact hex'.unique h2 (isResChar_chrMap ι h1)

/- English proof (translation)
Introduce `v`. Establish `mk' : ∀ (H : Subgroup (AfE F E)ˣ) (ζ : Chr F E K), ζ ∈ kills Kˣ H ↔ H ≤ ζ.ker` using `fun _ _ => Iff.rfl`. Use `first`. Consider the case `exact (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp μ.2).1).2) v`. Consider the case `(have h := μ.2; simp only [tupGrp, Subgroup.mem_inf, Subgroup.mem_iInf, mk'] at h; exact h.1.2 v)`.
-/
theorem tup_tame {S : Set ℕ} (μ : Tup F E K S) : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ (μ : Chr F E K).ker := by
  intro v
  have mk' : ∀ (H : Subgroup (AfE F E)ˣ) (ζ : Chr F E K), ζ ∈ kills Kˣ H ↔ H ≤ ζ.ker := fun _ _ => Iff.rfl
  first
  | exact (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp μ.2).1).2) v
  | (have h := μ.2; simp only [tupGrp, Subgroup.mem_inf, Subgroup.mem_iInf, mk'] at h; exact h.1.2 v)

end TupMap

section LevMap

variable {K L : Type} [Field K] [Field L] (ι : K →+* L)

def Lev.coefMap {κ : Type} [CommRing κ] {n : ℕ} (l : Lev κ K n) : Lev κ L n := ⟨l.H, (Units.map ι.toMonoidHom).comp l.lam⟩

/- English proof (translation)
Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations. Use `first`. Consider the case `simp only [MonoidHom.inv_apply, MonoidHom.comp_apply, map_inv]`. Consider the case `simp`.
-/
theorem coefMap_comp_inv {G : Type} [Group G] (f : G →* Kˣ) :
    ((Units.map ι.toMonoidHom).comp f)⁻¹ = (Units.map ι.toMonoidHom).comp f⁻¹ := by
  refine MonoidHom.ext fun x => ?_
  first
  | simp only [MonoidHom.inv_apply, MonoidHom.comp_apply, map_inv]
  | simp

/- English proof (translation)
Use `first`. Consider the case `exact congrArg (Lev.mk l.H) (coefMap_comp_inv ι l.lam)`. Consider the case `(show Lev.mk l.H ((Units.map ι.toMonoidHom).comp l.lam)⁻¹ = Lev.mk l.H ((Units.map ι.toMonoidHom).comp l.lam⁻¹)`. Conclude with `congrArg (Lev.mk l.H) (coefMap_comp_inv ι l.lam))`.
-/
theorem Lev.coefMap_inv {κ : Type} [CommRing κ] {n : ℕ} (l : Lev κ K n) : (l.coefMap ι).inv = l.inv.coefMap ι := by
  first
  | exact congrArg (Lev.mk l.H) (coefMap_comp_inv ι l.lam)
  | (show Lev.mk l.H ((Units.map ι.toMonoidHom).comp l.lam)⁻¹ = Lev.mk l.H ((Units.map ι.toMonoidHom).comp l.lam⁻¹)
     exact congrArg (Lev.mk l.H) (coefMap_comp_inv ι l.lam))

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def LevFam.coefMap {SG : Finset (HeightOneSpectrum (𝓞 E))} (Λ : LevFam E K n SG) : LevFam E L n SG :=
  fun w => (Λ w).coefMap ι

def LevFam.reidx {SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (h : SG = SG') (Λ : LevFam E K n SG') : LevFam E K n SG :=
  fun w => Λ ⟨w.1, h ▸ w.2⟩

/- English proof (translation)
Use function extensionality and compare the values at `w`. Conclude with `Lev.coefMap_inv ι (Λ w)`.
-/
theorem LevFam.coefMap_inv {SG : Finset (HeightOneSpectrum (𝓞 E))} (Λ : LevFam E K n SG) :
    (Λ.coefMap ι).inv = Λ.inv.coefMap ι := by
  funext w
  exact Lev.coefMap_inv ι (Λ w)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem LevFam.coefMap_reidx {SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (h : SG = SG') (Λ : LevFam E K n SG') :
    (Λ.reidx h).coefMap ι = (Λ.coefMap ι).reidx h := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem LevFam.inv_reidx {SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (h : SG = SG') (Λ : LevFam E K n SG') :
    (Λ.reidx h).inv = Λ.inv.reidx h := rfl

/- English proof (translation)
Substitute `hQ` using the available equality. Substitute `hA` using the available equality. Use function extensionality and compare the values at `w`. Distinguish the cases in `hw : w.1 ∈ SG`. Simplify using `only [LevFam.glue, LevFam.reidx, LevFam.coefMap, dif_pos hw]`.

Simplify using `only [LevFam.glue, LevFam.reidx, LevFam.coefMap, dif_neg hw]`. Conclude with `hB _`.
-/
theorem LevFam.glue_coefMap_reidx {SG Q₁ Q₂ : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q₁ = Q₂) (A : LevFam E K n SG)
    (A' : LevFam E L n SG) (B : LevFam E K n Q₂) (B' : LevFam E L n Q₁) (hA : A' = A.coefMap ι)
    (hB : ∀ P : Q₁, B' P = (B ⟨P.1, hQ ▸ P.2⟩).coefMap ι) :
    A'.glue B' = ((A.glue B).coefMap ι).reidx (congrArg (uSG SG) hQ) := by
  subst hQ
  subst hA
  funext w
  by_cases hw : w.1 ∈ SG
  · simp only [LevFam.glue, LevFam.reidx, LevFam.coefMap, dif_pos hw]
  · simp only [LevFam.glue, LevFam.reidx, LevFam.coefMap, dif_neg hw]
    exact hB _

/- English proof (translation)
Establish `key : ∀ y : ↥(Subgroup.pi Set.univ fun w : SG => (Λ w).H), (∏ i, ((Units.map ι.toMonoidHom).comp (Λ i).lam).comp (piProj (fun w : SG => (Λ w).H) i)) y = Units.map ι.toMonoidHom ((∏ i, (Λ i).lam.comp (piProj (fun w : SG => (Λ w).H) i)) y)`. Introduce `y`. Use `first`. Consider the case `simp only [MonoidHom.finset_prod_apply, MonoidHom.comp_apply, map_prod]`. Consider the case `simp [MonoidHom.finset_prod_apply, map_prod]`.

Use `first`. Consider the case `exact key x`. Consider the case `(simp only [LevFam.chr, piChar, LevFam.coefMap, Lev.coefMap]`. Conclude with `key x)`.
-/
theorem LevFam.coefMap_chr {SG : Finset (HeightOneSpectrum (𝓞 E))} (Λ : LevFam E K n SG) (x : ↥Λ.grp) :
    (Λ.coefMap ι).chr x = Units.map ι.toMonoidHom (Λ.chr x) := by
  have key : ∀ y : ↥(Subgroup.pi Set.univ fun w : SG => (Λ w).H),
      (∏ i, ((Units.map ι.toMonoidHom).comp (Λ i).lam).comp (piProj (fun w : SG => (Λ w).H) i)) y =
        Units.map ι.toMonoidHom ((∏ i, (Λ i).lam.comp (piProj (fun w : SG => (Λ w).H) i)) y) := by
    intro y
    first
    | simp only [MonoidHom.finset_prod_apply, MonoidHom.comp_apply, map_prod]
    | simp [MonoidHom.finset_prod_apply, map_prod]
  first
  | exact key x
  | (simp only [LevFam.chr, piChar, LevFam.coefMap, Lev.coefMap]
     exact key x)

end LevMap

section LevChars

variable {K L : Type} [Field K] [Field L] (ι : K →+* L) {κ : Type} [CommRing κ] {n : ℕ}

/- English proof (translation)
Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations. Use `first`. Consider the case `simp only [detChar, MonoidHom.finset_prod_apply, MonoidHom.comp_apply, map_prod]`. Consider the case `simp [detChar, map_prod]`.
-/
theorem detChar_coefMap (χ : ℕ → κˣ →* Kˣ) (a : ℕ) (bl : List ℕ) :
    detChar (fun s => (Units.map ι.toMonoidHom).comp (χ s)) n a bl = (Units.map ι.toMonoidHom).comp (detChar χ n a bl) := by
  refine MonoidHom.ext fun x => ?_
  first
  | simp only [detChar, MonoidHom.finset_prod_apply, MonoidHom.comp_apply, map_prod]
  | simp [detChar, map_prod]

/- English proof (translation)
Unfold `lamK`. Rewrite using `[detChar_coefMap, MonoidHom.comp_assoc]`.
-/
theorem lamK_coefMap (χ : ℕ → κˣ →* Kˣ) (r : ℕ) (bl : List ℕ) :
    lamK (fun s => (Units.map ι.toMonoidHom).comp (χ s)) n r bl = (Units.map ι.toMonoidHom).comp (lamK χ n r bl) := by
  unfold lamK
  rw [detChar_coefMap, MonoidHom.comp_assoc]

/- English proof (translation)
Unfold `lamQ`. Conclude with `detChar_coefMap ι (fun _ => ξ) a [b]`.
-/
theorem lamQ_coefMap (ξ : κˣ →* Kˣ) (a b : ℕ) :
    lamQ ((Units.map ι.toMonoidHom).comp ξ) n a b = (Units.map ι.toMonoidHom).comp (lamQ ξ n a b) := by
  unfold lamQ
  exact detChar_coefMap ι (fun _ => ξ) a [b]

/- English proof (translation)
Distinguish the cases in `h : s < m`. Simplify using `only [extChi, dif_pos h]`. Simplify using `only [extChi, dif_neg h, MonoidHom.comp_one]`.
-/
theorem extChi_coefMap {m : ℕ} (χ : Fin m → κˣ →* Kˣ) (s : ℕ) :
    extChi (fun j => (Units.map ι.toMonoidHom).comp (χ j)) s = (Units.map ι.toMonoidHom).comp (extChi χ s) := by
  by_cases h : s < m
  · simp only [extChi, dif_pos h]
  · simp only [extChi, dif_neg h, MonoidHom.comp_one]

/- English proof (translation)
Unfold `lamQP`. Rewrite using `[resChar_chrMap ι ξ ht P, lamQ_coefMap]`.
-/
theorem lambdaAtPrime_characterMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ξ : Chr F E K)
    (ht : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) (P : HeightOneSpectrum (𝓞 E)) (n a b : ℕ) :
    lamQP (chrMap ι ξ) P n a b = (Units.map ι.toMonoidHom).comp (lamQP ξ P n a b) := by
  unfold lamQP
  rw [resChar_chrMap ι ξ ht P, lamQ_coefMap]

end LevChars

open Classical in
/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem hfs_dite_finite {α β : Type} (f : α → β) {A B : Set α} (h : A = B) :
    (if h : A.Finite then h.toFinset.image f else ∅) = (if h : B.Finite then h.toFinset.image f else ∅) := by
  subst h
  rfl

section Ext

variable (X : Fields) (L : Type) [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)

@[reducible] def Fields.coefExt : Fields where
  F := X.F
  E := X.E
  K := L
  Tau := X.Tau
  emb τ := ι.comp (X.emb τ)

variable {X L ι}

@[reducible] def Primes.coefExt (Pr : Primes X) : Primes (X.coefExt L ι) where
  cond := Pr.cond
  g := Pr.g
  piG := Pr.piG
  Word := Pr.Word
  T := Pr.T
  piT := Pr.piT

@[reducible] def Wts.coefExt {Word : Type} {R : Ranks} (W : Wts X Word R) : Wts (X.coefExt L ι) Word R where
  row := W.row
  hc := W.hc
  tops := W.tops

@[reducible] def Chars.coefMap {Pr : Primes X} {m : ℕ} (Ch : Chars X Pr m) : Chars (X.coefExt L ι) (Pr.coefExt (L := L) (ι := ι)) m where
  psi0 w := ι.toMonoidHom.compAddChar (Ch.psi0 w)
  chi j w := (Units.map ι.toMonoidHom).comp (Ch.chi j w)
  muVal j v := Units.map ι.toMonoidHom (Ch.muVal j v)
  etaVal v := Units.map ι.toMonoidHom (Ch.etaVal v)

variable {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

/- English proof (translation)
Use `first`. Consider the case `(unfold chiAt; exact extChi_coefMap ι (fun j => Ch.chi j w) s)`. Consider the case `exact extChi_coefMap ι _ s`.
-/
theorem chiAt_coefMap (w : {w // w ∈ Pr.vGs}) (s : ℕ) :
    chiAt (Ch.coefMap (L := L) (ι := ι)) w s = (Units.map ι.toMonoidHom).comp (chiAt Ch w s) := by
  first
  | (unfold chiAt; exact extChi_coefMap ι (fun j => Ch.chi j w) s)
  | exact extChi_coefMap ι _ s

/- English proof (translation)
Establish `hχ : χ' = fun s => (Units.map φ.toMonoidHom).comp (χ s)` using `funext h`. Substitute `hχ` using the available equality. Conclude with `lamK_coefMap φ χ r bl`.
-/
private theorem lamK_comp_units_map {κ K₀ L₀ : Type} [CommRing κ] [Field K₀] [Field L₀] (φ : K₀ →+* L₀)
    (χ : ℕ → κˣ →* K₀ˣ) (χ' : ℕ → κˣ →* L₀ˣ) (h : ∀ s, χ' s = (Units.map φ.toMonoidHom).comp (χ s)) {n : ℕ} (r : ℕ)
    (bl : List ℕ) : lamK χ' n r bl = (Units.map φ.toMonoidHom).comp (lamK χ n r bl) := by
  have hχ : χ' = fun s => (Units.map φ.toMonoidHom).comp (χ s) := funext h
  subst hχ
  exact lamK_coefMap φ χ r bl

set_option maxHeartbeats 800000 in

/- English proof (translation)
Use function extensionality and compare the values at `w`. Conclude with `congrArg (Lev.mk _) (lamK_comp_units_map ι (chiAt Ch w) (chiAt (Ch.coefMap (L := L) (ι := ι)) w) (fun s => chiAt_coefMap Ch w s) _ _)`.
-/
theorem rowTyK_coefMap : rowTyK (R := R) (Ch.coefMap (L := L) (ι := ι)) = (rowTyK Ch).coefMap ι := by
  funext w
  exact congrArg (Lev.mk _) (lamK_comp_units_map ι (chiAt Ch w) (chiAt (Ch.coefMap (L := L) (ι := ι)) w)
    (fun s => chiAt_coefMap Ch w s) _ _)

set_option maxHeartbeats 800000 in

/- English proof (translation)
Use function extensionality and compare the values at `w`. Conclude with `congrArg (Lev.mk _) (lamK_comp_units_map ι (fun _ => (chiAt Ch w (j - 1))⁻¹) (fun _ => (chiAt (Ch.coefMap (L := L) (ι := ι)) w (j - 1))⁻¹) (fun _ => (congrArg (fun f => f⁻¹) (chiAt_coefMap Ch w (j - 1))).trans (coefMap_comp_inv ι _)) _ _)`.
-/
theorem mtTyK_coefMap (j : ℕ) : mtTyK (R := R) (Ch.coefMap (L := L) (ι := ι)) j = (mtTyK Ch j).coefMap ι := by
  funext w
  exact congrArg (Lev.mk _) (lamK_comp_units_map ι (fun _ => (chiAt Ch w (j - 1))⁻¹)
    (fun _ => (chiAt (Ch.coefMap (L := L) (ι := ι)) w (j - 1))⁻¹)
    (fun _ => (congrArg (fun f => f⁻¹) (chiAt_coefMap Ch w (j - 1))).trans (coefMap_comp_inv ι _)) _ _)

variable (R) in
/- English proof (translation)
Use `first`. Consider the case `exact congrArg (Lev.mk _) ((congrArg (fun f => f⁻¹) (lambdaAtPrime_characterMap ι _ (tup_tame μ) P.1 _ _ _)).trans (coefMap_comp_inv ι _))`. Consider the case `(show Lev.mk _ (lamQP (chrMap ι (μ : Chr X.F X.E X.K)) P.1 _ _ _)⁻¹ = Lev.mk _ ((Units.map ι.toMonoidHom).comp (lamQP (μ : Chr X.F X.E X.K) P.1 _ _ _)⁻¹)`. Rewrite using `[lambdaAtPrime_characterMap ι _ (tup_tame μ), coefMap_comp_inv])`.
-/
theorem rowTyQ_coefMap {S : Set ℕ} (μ : Tup X.F X.E X.K S) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (P : Q) :
    rowTyQ (X := X.coefExt L ι) R (chrMap ι (μ : Chr X.F X.E X.K)) Q P = (rowTyQ R (μ : Chr X.F X.E X.K) Q P).coefMap ι := by
  first
  | exact congrArg (Lev.mk _) ((congrArg (fun f => f⁻¹) (lambdaAtPrime_characterMap ι _ (tup_tame μ) P.1 _ _ _)).trans
      (coefMap_comp_inv ι _))
  | (show Lev.mk _ (lamQP (chrMap ι (μ : Chr X.F X.E X.K)) P.1 _ _ _)⁻¹ =
        Lev.mk _ ((Units.map ι.toMonoidHom).comp (lamQP (μ : Chr X.F X.E X.K) P.1 _ _ _)⁻¹)
     rw [lambdaAtPrime_characterMap ι _ (tup_tame μ), coefMap_comp_inv])

variable (R) in
/- English proof (translation)
Use `first`. Consider the case `exact congrArg (Lev.mk _) (lambdaAtPrime_characterMap ι _ (tup_tame μ) P.1 _ _ _)`. Consider the case `(show Lev.mk _ (lamQP (chrMap ι (μ : Chr X.F X.E X.K)) P.1 _ _ _) = Lev.mk _ ((Units.map ι.toMonoidHom).comp (lamQP (μ : Chr X.F X.E X.K) P.1 _ _ _))`. Rewrite using `[lambdaAtPrime_characterMap ι _ (tup_tame μ)])`.
-/
theorem mtTyQ_coefMap {S : Set ℕ} (μ : Tup X.F X.E X.K S) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (P : Q) :
    mtTyQ (X := X.coefExt L ι) R (chrMap ι (μ : Chr X.F X.E X.K)) Q P = (mtTyQ R (μ : Chr X.F X.E X.K) Q P).coefMap ι := by
  first
  | exact congrArg (Lev.mk _) (lambdaAtPrime_characterMap ι _ (tup_tame μ) P.1 _ _ _)
  | (show Lev.mk _ (lamQP (chrMap ι (μ : Chr X.F X.E X.K)) P.1 _ _ _) =
        Lev.mk _ ((Units.map ι.toMonoidHom).comp (lamQP (μ : Chr X.F X.E X.K) P.1 _ _ _))
     rw [lambdaAtPrime_characterMap ι _ (tup_tame μ)])

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}

/- English proof (translation)
Use `first`. Consider the case `(unfold QE; exact hfs_dite_finite sel (Qprime_chrMap ι ξ))`. Consider the case `simp only [QE, Qprime_chrMap]`.
-/
theorem QE_coefMap (ξ : Chr X.F X.E X.K) : QE (X := X.coefExt L ι) sel (chrMap ι ξ) = QE sel ξ := by
  first
  | (unfold QE; exact hfs_dite_finite sel (Qprime_chrMap ι ξ))
  | simp only [QE, Qprime_chrMap]

/- English proof (translation)
Use `first`. Consider the case `exact congrArg (uSG Pr.vGs) (QE_coefMap sel (μ : Chr X.F X.E X.K))`. Consider the case `simp only [rowSG, uSG, tupMap_coe, QE_coefMap]`.
-/
theorem rowSG_coefMap (μ : Tup X.F X.E X.K S) :
    rowSG (Pr.coefExt (L := L) (ι := ι)) sel (tupMap ι S μ) = rowSG Pr sel μ := by
  first
  | exact congrArg (uSG Pr.vGs) (QE_coefMap sel (μ : Chr X.F X.E X.K))
  | simp only [rowSG, uSG, tupMap_coe, QE_coefMap]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Use `first`. Consider the case `exact LevFam.glue_coefMap_reidx ι (QE_coefMap sel (μ : Chr X.F X.E X.K)) _ _ _ _ (rowTyK_coefMap Ch) (fun P => rowTyQ_coefMap R μ _ P)`. Consider the case `(unfold rowTyKK`. Conclude with `LevFam.glue_coefMap_reidx ι (QE_coefMap sel (μ : Chr X.F X.E X.K)) _ _ _ _ (rowTyK_coefMap Ch) (fun P => by`. Simplify using `only [rowTyQ, Lev.coefMap, lambdaAtPrime_characterMap ι (μ : Chr X.F X.E X.K) (tup_tame μ), coefMap_comp_inv]))`.
-/
theorem rowTyKK_coefMap (μ : Tup X.F X.E X.K S) :
    rowTyKK (Ch.coefMap (L := L) (ι := ι)) sel (tupMap ι S μ) =
      ((rowTyKK Ch sel μ).coefMap ι).reidx (rowSG_coefMap sel μ) := by
  first
  | exact LevFam.glue_coefMap_reidx ι (QE_coefMap sel (μ : Chr X.F X.E X.K)) _ _ _ _ (rowTyK_coefMap Ch)
      (fun P => rowTyQ_coefMap R μ _ P)
  | (unfold rowTyKK
     exact LevFam.glue_coefMap_reidx ι (QE_coefMap sel (μ : Chr X.F X.E X.K)) _ _ _ _ (rowTyK_coefMap Ch)
      (fun P => by
        simp only [rowTyQ, Lev.coefMap, lambdaAtPrime_characterMap ι (μ : Chr X.F X.E X.K) (tup_tame μ), coefMap_comp_inv]))

set_option maxHeartbeats 800000 in

/- English proof (translation)
Use `first`. Consider the case `exact LevFam.glue_coefMap_reidx ι (QE_coefMap sel (μ : Chr X.F X.E X.K)) _ _ _ _ (mtTyK_coefMap Ch j) (fun P => mtTyQ_coefMap R μ _ P)`. Consider the case `(unfold mtTyKK`. Conclude with `LevFam.glue_coefMap_reidx ι (QE_coefMap sel (μ : Chr X.F X.E X.K)) _ _ _ _ (mtTyK_coefMap Ch j) (fun P => by simp only [mtTyQ, Lev.coefMap, lambdaAtPrime_characterMap ι (μ : Chr X.F X.E X.K) (tup_tame μ)]))`.
-/
theorem mtTyKK_coefMap (μ : Tup X.F X.E X.K S) (j : ℕ) :
    mtTyKK (Ch.coefMap (L := L) (ι := ι)) sel (tupMap ι S μ) j =
      ((mtTyKK Ch sel μ j).coefMap ι).reidx (rowSG_coefMap sel μ) := by
  first
  | exact LevFam.glue_coefMap_reidx ι (QE_coefMap sel (μ : Chr X.F X.E X.K)) _ _ _ _ (mtTyK_coefMap Ch j)
      (fun P => mtTyQ_coefMap R μ _ P)
  | (unfold mtTyKK
     exact LevFam.glue_coefMap_reidx ι (QE_coefMap sel (μ : Chr X.F X.E X.K)) _ _ _ _ (mtTyK_coefMap Ch j)
      (fun P => by simp only [mtTyQ, Lev.coefMap, lambdaAtPrime_characterMap ι (μ : Chr X.F X.E X.K) (tup_tame μ)]))

end Ext

end Formalism.L2.Col
