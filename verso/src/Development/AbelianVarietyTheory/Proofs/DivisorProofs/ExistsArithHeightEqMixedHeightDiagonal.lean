import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArithStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableOfProjArithAmbientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchIntegralAdditiveAndDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightPowEqDegreeLogCardFiniteFieldStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHtDiag

/- English proof (translation)
Rewrite using `[i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq]`. Conclude with `topologicalKrullDim_subspace_le X (Set.range i)`.
-/
theorem dim_le_of_isClosedImmersion {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] :
    topologicalKrullDim Z ≤ topologicalKrullDim X := by
  rw [i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq]
  exact topologicalKrullDim_subspace_le X (Set.range i)

/- English proof (translation)
Use `Nat.card_eq_of_bijective (i.residueFieldMap z) ⟨(i.residueFieldMap z).hom.injective, fun a => ?_⟩` and prove the remaining obligations. Take `⟨b, rfl⟩` from `Z.residue_surjective z a`. Take `⟨c, rfl⟩` from `i.stalkMap_surjective z b`. Conclude with `⟨X.residue _ c, (ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i z) c :)⟩`.
-/
theorem card_residueField_eq {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    Nat.card (X.residueField (i z)) = Nat.card (Z.residueField z) := by
  refine Nat.card_eq_of_bijective (i.residueFieldMap z) ⟨(i.residueFieldMap z).hom.injective, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := Z.residue_surjective z a
  obtain ⟨c, rfl⟩ := i.stalkMap_surjective z b
  exact ⟨X.residue _ c, (ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i z) c :)⟩

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

/- English proof (translation)
Establish `hiso (A B : HermLB p) (h : A.Isometric B) : T (e + 1) (Fin.cons A L) x = T (e + 1) (Fin.cons B L) x` using `hT.iso (e + 1) _ _ x he hx fun a => Fin.cases h (fun j => HermLB.Isometric.refl (L j)) a`. Establish `h0 : T (e + 1) (Fin.cons (HermLB.triv p) L) x = 0`. Use `hT.add e (HermLB.triv p) (HermLB.triv p) L x he hx` as an intermediate fact. Rewrite `this` using `[hiso _ _ (HermLB.triv p).isometric_tens_triv]`. Combine the linear equalities and inequalities to obtain the conclusion.

Proceed by induction on `n with`. Consider the case `zero => rw [hiso _ _ N.isometric_pow_zero, h0]`. Simplify using the standard rewrite rules. Consider the case `succ n ih => rw [hiso _ _ (N.isometric_pow_succ n), hT.add e _ _ L x he hx, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mix_pow {m : ℕ} {T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ} (hT : IsMix p m T) (e : ℕ) (N : HermLB p)
    (L : Fin e → HermLB p) (x : X) (he : e + 1 ≤ m) (hx : HasDim x (e + 1)) (n : ℕ) :
    T (e + 1) (Fin.cons (N.pow n) L) x = n * T (e + 1) (Fin.cons N L) x := by
  have hiso (A B : HermLB p) (h : A.Isometric B) :
      T (e + 1) (Fin.cons A L) x = T (e + 1) (Fin.cons B L) x :=
    hT.iso (e + 1) _ _ x he hx fun a => Fin.cases h (fun j => HermLB.Isometric.refl (L j)) a
  have h0 : T (e + 1) (Fin.cons (HermLB.triv p) L) x = 0 := by
    have := hT.add e (HermLB.triv p) (HermLB.triv p) L x he hx
    rw [hiso _ _ (HermLB.triv p).isometric_tens_triv] at this
    linarith
  induction n with
  | zero => rw [hiso _ _ N.isometric_pow_zero, h0]; simp
  | succ n ih => rw [hiso _ _ (N.isometric_pow_succ n), hT.add e _ _ L x he hx, ih]; push_cast; ring

/- English proof (translation)
Introduce `HI k _ X p D hX T hT N`. Establish `hA : IsAmb p` using `isAmb_of_isArithVar hX`. Take `⟨-, -, -, -, himm, hgen⟩` from `GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hA`. Set `h : X → ℝ` to `fun x => T ((topologicalKrullDim (closure ({x} : Set X))).unbotD 0).toNat (fun _ => N) x`. Establish `hh (x : X) (d : ℕ) (hd : HasDim x d) : h x = T d (fun _ => N) x`.

Establish `hd' : topologicalKrullDim (closure ({x} : Set X)) = d` using `hd`. Use `show T ((topologicalKrullDim (closure ({x} : Set X))).unbotD 0).toNat (fun _ => N) x = _`. Rewrite using `[hd']`. Both sides reduce to the same expression. Establish `hle (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z = d) : d ≤ D + 1`.

Use `dim_le_of_isClosedImmersion i` as an intermediate fact. Rewrite `this` using `[hd, hX.dim_eq]`. Conclude with `this` after adjusting the coercions. Establish `hgi (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (d : ℕ) (hd : topologicalKrullDim Z = d) : HasDim (i (genericPoint Z)) d` using `(himm Z i _ d).2 ((hgen Z d).2 hd)`. Use `⟨h, ⟨fun Z i _ _ κ _ _ _ d hd => ?_, fun Z i _ _ _ hc hd r hr => ?_, fun Z i _ _ _ hc e he hd m r hr => ?_⟩, hh⟩` and prove the remaining obligations.

Rewrite using `[hh _ d (hgi Z i d hd)]`. Conclude with `GlobalTheory.T.mixedHeight_pow_eq_degree_log_card_finiteField k X p hA (D + 1) T hT N d (hle Z i d hd) Z i κ hd`. Establish `hd1 : topologicalKrullDim Z = ((0 + 1 : ℕ) : WithBot ℕ∞)` using `by rw [hd]; rfl`. Establish `hZ : IsArithVar (i ≫ p) 0` using `hX.of_isClosedImmersion i hc hd1`. Establish `hAZ : IsAmb (i ≫ p)` using `hA.sub i`.

Establish `key : T 1 (fun _ => N) (i (genericPoint Z)) = recVal (fun z => T 0 (fun _ => N) (i z)) (fun _ : Fin 0 => N.restr i) (N.restr i) hr`. Use `hT.recur Z (i ≫ p) i rfl 0 (by omega) hd1 N (fun _ => N) (N.restr i) (fun _ => N.restr i) (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) r hr` as an intermediate fact. Use `Eq.trans ?_ this` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `a`.

Conclude with `Fin.cases rfl (fun j => j.elim0) a`. Rewrite using `[hh _ 1 (hgi Z i 1 hd1), key, recVal, (GlobalTheory.T.mixedArchIntegral_additive_and_diagonal HI k Z (i ≫ p) hAZ (N.restr i) r hr).2 0 hd1 (N.restr i), GlobalTheory.ArchDimZero.main k Z (i ≫ p) hZ _ _ r hr, HermLB.curveDeg]`. Use `congrArg (· - _) (finsum_congr fun z => ?_)` and prove the remaining obligations. Distinguish the cases in `hz : ((N.restr i).div hr).mult z = 0`. Simplify using `[hz]`.

Establish `hz1` using `CartierDiv.coheight_eq_one_of_mult_ne_zero hz`. Establish `hz0 : HasDim (i z) 0` using `(himm Z i z 0).2 (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Z (i ≫ p) hAZ 0 hd1).1 z).1 hz1)`. Rewrite using `[hT.zero _ _ hz0, card_residueField_eq i z]`. Establish `hAZ : IsAmb (i ≫ p)` using `hA.sub i`. Use `⟨GlobalTheory.T.archIntegrable_of_projArithAmbient HI k Z (i ≫ p) hAZ e hd _ _ r hr, ?_⟩` and prove the remaining obligations.

Establish `hle'` using `hle Z i (e + 1) hd`. Establish `hx` using `hgi Z i (e + 1) hd`. Establish `hiso : ((N.pow m).pull i rfl).Isometric ((N.restr i).pow m)` using `HermLB.icls_eq_iff.1 (by simp only [HermLB.icls_pull, HermLB.icls_pow, map_nsmul])`. Establish `key` using `hT.recur Z (i ≫ p) i rfl e hle' hd (N.pow m) (fun _ => N) ((N.restr i).pow m) (fun _ => N.restr i) hiso (fun _ => HermLB.Isometric.refl _) r hr`. Rewrite `key` using `[mix_pow hT e N (fun _ => N) _ hle' hx m]`.

Establish `e1 : (Fin.cons N (fun _ : Fin e => N) : Fin (e + 1) → HermLB p) = fun _ => N`. Use function extensionality and compare the values at `fun a => Fin.cases rfl (fun _ => rfl) a`. Rewrite `key` using `[e1]`. Rewrite using `[hh _ (e + 1) hx, key, recVal, (GlobalTheory.T.mixedArchIntegral_additive_and_diagonal HI k Z (i ≫ p) hAZ ((N.restr i).pow m) r hr).2 e hd (N.restr i)]`. Use `congrArg (· - _) (finsum_congr fun z => ?_)` and prove the remaining obligations.

Distinguish the cases in `hz : (((N.restr i).pow m).div hr).mult z = 0`. Simplify using `[hz]`. Establish `hz1` using `CartierDiv.coheight_eq_one_of_mult_ne_zero hz`. Establish `hze : HasDim (i z) e` using `(himm Z i z e).2 (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Z (i ≫ p) hAZ e hd).1 z).1 hz1)`. Rewrite using `[hh _ e hze]`.
-/
theorem exists_isArithHeight : ArchInteg → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ T, IsMix p (D + 1) T → ∀ N : HermLB p, ∃ h : X → ℝ, N.IsArithHeight h ∧ ∀ (x : X) (d : ℕ), HasDim x d → h x = T d (fun _ => N) x := by
  intro HI k _ X p D hX T hT N
  have hA : IsAmb p := isAmb_of_isArithVar hX
  obtain ⟨-, -, -, -, himm, hgen⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hA
  let h : X → ℝ := fun x =>
    T ((topologicalKrullDim (closure ({x} : Set X))).unbotD 0).toNat (fun _ => N) x
  have hh (x : X) (d : ℕ) (hd : HasDim x d) : h x = T d (fun _ => N) x := by
    have hd' : topologicalKrullDim (closure ({x} : Set X)) = d := hd
    show T ((topologicalKrullDim (closure ({x} : Set X))).unbotD 0).toNat (fun _ => N) x = _
    rw [hd']
    rfl
  have hle (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z = d) :
      d ≤ D + 1 := by
    have := dim_le_of_isClosedImmersion i
    rw [hd, hX.dim_eq] at this
    exact_mod_cast this
  have hgi (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (d : ℕ)
      (hd : topologicalKrullDim Z = d) : HasDim (i (genericPoint Z)) d :=
    (himm Z i _ d).2 ((hgen Z d).2 hd)
  refine ⟨h, ⟨fun Z i _ _ κ _ _ _ d hd => ?_, fun Z i _ _ _ hc hd r hr => ?_,
    fun Z i _ _ _ hc e he hd m r hr => ?_⟩, hh⟩
  · rw [hh _ d (hgi Z i d hd)]
    exact GlobalTheory.T.mixedHeight_pow_eq_degree_log_card_finiteField k X p hA (D + 1) T hT N d (hle Z i d hd) Z i κ hd
  · have hd1 : topologicalKrullDim Z = ((0 + 1 : ℕ) : WithBot ℕ∞) := by rw [hd]; rfl
    have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd1
    have hAZ : IsAmb (i ≫ p) := hA.sub i
    have key : T 1 (fun _ => N) (i (genericPoint Z)) =
        recVal (fun z => T 0 (fun _ => N) (i z)) (fun _ : Fin 0 => N.restr i) (N.restr i) hr := by
      have := hT.recur Z (i ≫ p) i rfl 0 (by omega) hd1 N (fun _ => N) (N.restr i) (fun _ => N.restr i)
        (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) r hr
      refine Eq.trans ?_ this
      congr 1
      funext a
      exact Fin.cases rfl (fun j => j.elim0) a
    rw [hh _ 1 (hgi Z i 1 hd1), key, recVal, (GlobalTheory.T.mixedArchIntegral_additive_and_diagonal HI k Z (i ≫ p) hAZ (N.restr i) r hr).2 0 hd1 (N.restr i),
      GlobalTheory.ArchDimZero.main k Z (i ≫ p) hZ _ _ r hr, HermLB.curveDeg]
    refine congrArg (· - _) (finsum_congr fun z => ?_)
    by_cases hz : ((N.restr i).div hr).mult z = 0
    · simp [hz]
    have hz1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hz
    have hz0 : HasDim (i z) 0 := (himm Z i z 0).2 (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Z (i ≫ p) hAZ 0 hd1).1 z).1 hz1)
    rw [hT.zero _ _ hz0, card_residueField_eq i z]
  · have hAZ : IsAmb (i ≫ p) := hA.sub i
    refine ⟨GlobalTheory.T.archIntegrable_of_projArithAmbient HI k Z (i ≫ p) hAZ e hd _ _ r hr, ?_⟩
    have hle' := hle Z i (e + 1) hd
    have hx := hgi Z i (e + 1) hd
    have hiso : ((N.pow m).pull i rfl).Isometric ((N.restr i).pow m) :=
      HermLB.icls_eq_iff.1 (by simp only [HermLB.icls_pull, HermLB.icls_pow, map_nsmul])
    have key := hT.recur Z (i ≫ p) i rfl e hle' hd (N.pow m) (fun _ => N) ((N.restr i).pow m)
      (fun _ => N.restr i) hiso (fun _ => HermLB.Isometric.refl _) r hr
    rw [mix_pow hT e N (fun _ => N) _ hle' hx m] at key
    have e1 : (Fin.cons N (fun _ : Fin e => N) : Fin (e + 1) → HermLB p) = fun _ => N :=
      funext fun a => Fin.cases rfl (fun _ => rfl) a
    rw [e1] at key
    rw [hh _ (e + 1) hx, key, recVal, (GlobalTheory.T.mixedArchIntegral_additive_and_diagonal HI k Z (i ≫ p) hAZ ((N.restr i).pow m) r hr).2 e hd (N.restr i)]
    refine congrArg (· - _) (finsum_congr fun z => ?_)
    by_cases hz : (((N.restr i).pow m).div hr).mult z = 0
    · simp [hz]
    have hz1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hz
    have hze : HasDim (i z) e := (himm Z i z e).2 (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Z (i ≫ p) hAZ e hd).1 z).1 hz1)
    rw [hh _ e hze]

end GlobalTheory.MixHtDiag
