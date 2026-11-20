import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAlongIdIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring
open GlobalTheory.CechPic GlobalTheory.PrincipalIntegral GlobalTheory.KTrivSpread

noncomputable section

namespace GlobalTheory.PrincSubring

section Calc

variable {S : Scheme.{0}} {A : Over S} {n : ℕ}
variable [GrpObj A] [IsCommMonObj A] {π : Pic (A ⊗ A).left}
  (hadd : ∀ (T : Over S) (x x' y : T ⟶ A), pair π (x * x') y = pair π x y + pair π x' y)
  (hsym : ∀ (T : Over S) (x y : T ⟶ A), pair π x y = pair π y x)
variable {G : Over S} [GrpObj G] {pr : Fin n → (G ⟶ A)} (hmon : ∀ u, IsMonHom (pr u))
  (huniv : ∀ (T : Over S) (y : Fin n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u)
  {W : Matrix (Fin n) (Fin n) ℤ} {L : LB G.left} (hL : L.IsLB) (hLW : cls L hL = quad π W pr)

include hadd hsym hLW hmon huniv in

/- English proof (translation)
Introduce `T a ha x hx`. Establish `hd : (Out.translDiff G L x).IsLB` using `LB.isLB_linComb hL _ _`. Take `⟨z, -, hz⟩` from `huniv T fun _ => 1`. Use `(hz x fun u₀ => ?_).trans (hz (1 : T ⟶ G) fun u => ?_).symm` and prove the remaining obligations. Use `swap`.

Use `hmon u` as an intermediate fact. Conclude with `MonObj.one_comp _`. Use `choose V hV c hc using hx`. Use `Over.OverMorphism.ext (Scheme.Cover.hom_ext (T.left.openCoverOfIsOpenCover V (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hV p⟩)) _ _ fun p => ?_)` and prove the remaining obligations. Set `T' : Over S` to `Over.mk ((V p).ι ≫ T.hom)`.

Set `j : T' ⟶ T` to `Over.homMk (V p).ι rfl`. Establish `key : ∀ w : Fin n → ℤ, quad π W (fun u => (snd A T' ≫ j) ≫ x ≫ pr u) + ∑ u, ((W + W.transpose).mulVec w) u • pair π ((snd A T' ≫ j) ≫ x ≫ pr u) (fst A T') = 0` using `fun w => by`. Take `⟨b, hb, -⟩` from `huniv (A ⊗ T') fun v => fst A T' ^ w v`. Establish `h` using `pull_translDiff hadd hsym hmon hL hLW x (snd A T' ≫ j) b hd`. Establish `k : (lift (snd A T' ≫ j) b).left ≫ (fst T G).left = (snd A T').left ≫ (V p).ι` using `congrArg (fun q => q.left) (lift_fst (snd A T' ≫ j) b)`.

Take `⟨m, hm⟩ : ∃ m : (A ⊗ T').left ⟶ ((fst T G).left ⁻¹ᵁ V p).toScheme, m ≫ ((fst T G).left ⁻¹ᵁ V p).ι = (lift (snd A T' ≫ j) b).left` from `⟨IsOpenImmersion.lift _ (lift (snd A T' ≫ j) b).left (by`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `(congrArg (fun q => q y ∈ V p) k).mpr ((snd A T').left y).2), IsOpenImmersion.lift_fac _ _ _⟩`. Establish `h0` using `(cls_eq_zero_iff (pull_isLB hd _)).2 ⟨c p, hc p⟩`.

Rewrite `h0` using `[cls_pull hd]`. Rewrite `h` using `[← hm, pull_comp, h0, map_zero]`. Rewrite using `[h]`. Use `congr 1`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec, dotProduct, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[hb, hsym _ _ (fst A T' ^ w v), pair_zpow hadd, hsym _ (fst A T'), mul_smul]`. Establish `k₀` using `key 0`. Establish `k₁` using `key ((W + W.transpose).adjugate.mulVec (Pi.single u₀ 1))`.

Rewrite `k₁` using `[Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mulVec]`. Simplify using `only [Matrix.mulVec_zero, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at k₀`. Rewrite `k₁` using `[k₀, zero_add, Finset.sum_eq_single u₀ (fun v _ hv => by rw [Pi.single_eq_of_ne hv, zero_smul]) (by simp), Pi.single_eq_same, one_smul, Category.assoc]`. Establish `e : j ≫ x ≫ pr u₀ = j ≫ 1` using `(hker T' ((V p).ι ≫ a) (by simp [T', ha]) _ k₁).trans (MonObj.comp_one j).symm`. Conclude with `congrArg (fun q => q.left) e`.
-/
theorem trivAlong_of_kernelAlong {S' : Scheme.{0}} (g : S' ⟶ S) (hdet : (W + W.transpose).det = 1)
    (hker : ∀ (T : Over S) (a : T.left ⟶ S'), a ≫ g = T.hom → ∀ x : T ⟶ A,
      pair π (snd A T ≫ x) (fst A T) = 0 → x = 1) : TrivAlong G L g := by
  intro T a ha x hx
  have hd : (Out.translDiff G L x).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨z, -, hz⟩ := huniv T fun _ => 1
  refine (hz x fun u₀ => ?_).trans (hz (1 : T ⟶ G) fun u => ?_).symm
  swap
  · have := hmon u
    exact MonObj.one_comp _
  choose V hV c hc using hx
  refine Over.OverMorphism.ext (Scheme.Cover.hom_ext
    (T.left.openCoverOfIsOpenCover V
      (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hV p⟩)) _ _ fun p => ?_)
  let T' : Over S := Over.mk ((V p).ι ≫ T.hom)
  let j : T' ⟶ T := Over.homMk (V p).ι rfl
  have key : ∀ w : Fin n → ℤ, quad π W (fun u => (snd A T' ≫ j) ≫ x ≫ pr u) +
      ∑ u, ((W + W.transpose).mulVec w) u • pair π ((snd A T' ≫ j) ≫ x ≫ pr u) (fst A T') = 0 := fun w => by
    obtain ⟨b, hb, -⟩ := huniv (A ⊗ T') fun v => fst A T' ^ w v
    have h := pull_translDiff hadd hsym hmon hL hLW x (snd A T' ≫ j) b hd
    have k : (lift (snd A T' ≫ j) b).left ≫ (fst T G).left = (snd A T').left ≫ (V p).ι :=
      congrArg (fun q => q.left) (lift_fst (snd A T' ≫ j) b)
    obtain ⟨m, hm⟩ : ∃ m : (A ⊗ T').left ⟶ ((fst T G).left ⁻¹ᵁ V p).toScheme,
        m ≫ ((fst T G).left ⁻¹ᵁ V p).ι = (lift (snd A T' ≫ j) b).left :=
      ⟨IsOpenImmersion.lift _ (lift (snd A T' ≫ j) b).left (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y ∈ V p) k).mpr ((snd A T').left y).2), IsOpenImmersion.lift_fac _ _ _⟩
    have h0 := (cls_eq_zero_iff (pull_isLB hd _)).2 ⟨c p, hc p⟩
    rw [cls_pull hd] at h0
    rw [← hm, pull_comp, h0, map_zero] at h
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hb, hsym _ _ (fst A T' ^ w v), pair_zpow hadd, hsym _ (fst A T'), mul_smul]
  have k₀ := key 0
  have k₁ := key ((W + W.transpose).adjugate.mulVec (Pi.single u₀ 1))
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mulVec] at k₁
  simp only [Matrix.mulVec_zero, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at k₀
  rw [k₀, zero_add, Finset.sum_eq_single u₀ (fun v _ hv => by rw [Pi.single_eq_of_ne hv, zero_smul]) (by simp),
    Pi.single_eq_same, one_smul, Category.assoc] at k₁
  have e : j ≫ x ≫ pr u₀ = j ≫ 1 :=
    (hker T' ((V p).ι ≫ a) (by simp [T', ha]) _ k₁).trans (MonObj.comp_one j).symm
  exact congrArg (fun q => q.left) e

include hadd hsym hLW hmon huniv in

/- English proof (translation)
Take `⟨y, hy, -⟩` from `huniv T fun u => if u = u₀ then x else 1`. Establish `hz : ∀ (Z : Over S) (b : Z ⟶ T) (z : Z ⟶ A) u, pair π (b ≫ y ≫ pr u) z = 0` using `fun Z b z u => by`. Rewrite using `[hy]`. Use `split_ifs`. Establish `h` using `congrArg (pull (lift z b).left) hx`.

Rewrite `h` using `[pull_pair, map_zero, lift_snd_assoc, lift_fst]`. Then use the resulting hypothesis. Rewrite using `[MonObj.comp_one, pair_one hadd]`. Establish `hd : (Out.translDiff G L y).IsLB` using `LB.isLB_linComb hL _ _`. Establish `h1 : y = 1` using `hK T a ha y fun p => ⟨⊤, trivial, by`. Use `(cls_eq_zero_iff (pull_isLB hd _)).1 ?_` and prove the remaining obligations.

Establish `h` using `pull_translDiff hadd hsym hmon hL hLW y (fst T G) (snd T G) hd`. Simplify using `only [quad, hz, smul_zero, Finset.sum_const_zero, add_zero, lift_fst_snd, Over.id_left] at h`. Rewrite `h` using `[pull_id]`. Rewrite using `[cls_pull hd]`. Conclude with `(congrArg _ h).trans (map_zero _)⟩`.

Use `hmon u₀` as an intermediate fact. Establish `h` using `hy u₀`. Rewrite `h` using `[if_pos rfl, h1, MonObj.one_comp]`. Conclude with `h.symm`.
-/
theorem kernelAlong_of_trivAlong {S' : Scheme.{0}} (g : S' ⟶ S) (u₀ : Fin n) (hK : TrivAlong G L g)
    (T : Over S) (a : T.left ⟶ S') (ha : a ≫ g = T.hom) (x : T ⟶ A)
    (hx : pair π (snd A T ≫ x) (fst A T) = 0) : x = 1 := by
  obtain ⟨y, hy, -⟩ := huniv T fun u => if u = u₀ then x else 1
  have hz : ∀ (Z : Over S) (b : Z ⟶ T) (z : Z ⟶ A) u, pair π (b ≫ y ≫ pr u) z = 0 := fun Z b z u => by
    rw [hy]
    split_ifs
    · have h := congrArg (pull (lift z b).left) hx
      rwa [pull_pair, map_zero, lift_snd_assoc, lift_fst] at h
    · rw [MonObj.comp_one, pair_one hadd]
  have hd : (Out.translDiff G L y).IsLB := LB.isLB_linComb hL _ _
  have h1 : y = 1 := hK T a ha y fun p => ⟨⊤, trivial, by
    refine (cls_eq_zero_iff (pull_isLB hd _)).1 ?_
    have h := pull_translDiff hadd hsym hmon hL hLW y (fst T G) (snd T G) hd
    simp only [quad, hz, smul_zero, Finset.sum_const_zero, add_zero, lift_fst_snd, Over.id_left] at h
    rw [pull_id] at h
    rw [cls_pull hd]
    exact (congrArg _ h).trans (map_zero _)⟩
  have := hmon u₀
  have h := hy u₀
  rw [if_pos rfl, h1, MonObj.one_comp] at h
  exact h.symm

end Calc

/- English proof (translation)
Introduce `S h A _ _ P hs hA S' g`. Take `⟨hab, -, hP, hr₁, hr₂, hsw⟩` from `hs`. Establish `hadd : ∀ (T : Over S) (x x' y : T ⟶ A), pair (cls P hP) (x * x') y = pair (cls P hP) x y + pair (cls P hP) x' y` using `fun T x x' y => by`. Establish `e` using `(cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (Biadditive.biadditive_of_triv_axes globalFns_holds S A (diagPull A P) hab (pull_isLB hP _) hA P hP hr₁ hr₂ T x x' y).1`. Rewrite `e` using `[cls_linComb hP, Fin.sum_univ_three]`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e`. Rewrite using `[← sub_eq_zero, ← e]`. Unfold `PrincipalIntegral.pair`. Normalize the expressions using the abelian group laws. Establish `hsym : ∀ (T : Over S) (x y : T ⟶ A), pair (cls P hP) x y = pair (cls P hP) y x` using `fun T x y => by`.

Establish `e : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP)` using `(cls_eq_iff hP (pull_isLB hP _)).2 hsw`. Establish `k : (lift y x).left ≫ (lift (snd A A) (fst A A)).left = (lift x y).left`. Rewrite using `[← Over.comp_left, comp_lift, lift_fst, lift_snd]`. Unfold `PrincipalIntegral.pair`. Rewrite using `[← k, pull_comp, ← e]`.

Take `⟨-, hdet⟩` from `isE8_W8`. Establish `hmon : ∀ u : Fin 8, IsMonHom (Out.powPr A u)` using `fun u => inferInstance`. Establish `huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ Out.powObj A 8, ∀ u, x ≫ Out.powPr A u = y u` using `fun T y => ⟨(Out.powIsLimit A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit A 8).fac (Fan.mk T y) ⟨u⟩, fun x hx => (Out.powIsLimit A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩`. Establish `hL : (powLB A P).IsLB` using `LB.isLB_linComb hP _ _`. Establish `hLW : cls (powLB A P) hL = quad (cls P hP) GlobalTheory.W8 (Out.powPr A)` using `cls_linComb hP _ _ _`.

Establish `tr : ∀ (T : Over S) (x : T ⟶ A), pair (cls P hP) (snd A T ≫ x) (fst A T) = 0 ↔ IsTrivial (slice A P x)` using `fun T x => by`. Rewrite using `[PrincipalIntegral.pair, ← cls_pull hP _ (pull_isLB hP _)]`. Conclude with `(cls_eq_zero_iff _).trans (GlobalTheory.SiegelTypings.triv_swap hP x)`. Prove the components needed by the constructor for the conclusion. Introduce `hk`.

Conclude with `trivAlong_of_kernelAlong hadd hsym hmon huniv hL hLW g hdet fun T a ha x hx => hk T a ha x ((tr T x).1 hx)`. Introduce `hK T a ha x hx`. Conclude with `kernelAlong_of_trivAlong hadd hsym hmon huniv hL hLW g 0 hK T a ha x ((tr T x).2 hx)`.
-/
theorem kerAlong_iff_trivAlong : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (P : LB (A ⊗ A).left), IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → ∀ {S' : Scheme.{0}}
    (g : S' ⟶ S), KerAlong A P g ↔ GlobalTheory.KTrivSpread.TrivAlong (Out.powObj A 8) (powLB A P) g := by
  intro S h A _ _ P hs hA S' g
  obtain ⟨hab, -, hP, hr₁, hr₂, hsw⟩ := hs
  have hadd : ∀ (T : Over S) (x x' y : T ⟶ A),
      pair (cls P hP) (x * x') y = pair (cls P hP) x y + pair (cls P hP) x' y := fun T x x' y => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (Biadditive.biadditive_of_triv_axes globalFns_holds S A
      (diagPull A P) hab (pull_isLB hP _) hA P hP hr₁ hr₂ T x x' y).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    unfold PrincipalIntegral.pair
    abel
  have hsym : ∀ (T : Over S) (x y : T ⟶ A), pair (cls P hP) x y = pair (cls P hP) y x := fun T x y => by
    have e : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) :=
      (cls_eq_iff hP (pull_isLB hP _)).2 hsw
    have k : (lift y x).left ≫ (lift (snd A A) (fst A A)).left = (lift x y).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
    unfold PrincipalIntegral.pair
    rw [← k, pull_comp, ← e]
  obtain ⟨-, hdet⟩ := isE8_W8
  have hmon : ∀ u : Fin 8, IsMonHom (Out.powPr A u) := fun u => inferInstance
  have huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ Out.powObj A 8, ∀ u, x ≫ Out.powPr A u = y u :=
    fun T y => ⟨(Out.powIsLimit A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hL : (powLB A P).IsLB := LB.isLB_linComb hP _ _
  have hLW : cls (powLB A P) hL = quad (cls P hP) GlobalTheory.W8 (Out.powPr A) := cls_linComb hP _ _ _
  have tr : ∀ (T : Over S) (x : T ⟶ A), pair (cls P hP) (snd A T ≫ x) (fst A T) = 0 ↔ IsTrivial (slice A P x) :=
    fun T x => by
      rw [PrincipalIntegral.pair, ← cls_pull hP _ (pull_isLB hP _)]
      exact (cls_eq_zero_iff _).trans (GlobalTheory.SiegelTypings.triv_swap hP x)
  constructor
  · intro hk
    exact trivAlong_of_kernelAlong hadd hsym hmon huniv hL hLW g hdet fun T a ha x hx => hk T a ha x ((tr T x).1 hx)
  · intro hK T a ha x hx
    exact kernelAlong_of_trivAlong hadd hsym hmon huniv hL hLW g 0 hK T a ha x ((tr T x).2 hx)

end GlobalTheory.PrincSubring
