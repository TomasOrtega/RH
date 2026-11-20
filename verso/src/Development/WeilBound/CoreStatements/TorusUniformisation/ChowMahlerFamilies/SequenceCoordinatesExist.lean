import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceCoordinates

/- English proof (translation)
Set `I : Ideal R` to `{ carrier := {v | x * (v : Ω) ∈ R} add_mem' := fun {a b} ha hb => by`. Use `R.add_mem ha hb` as an intermediate fact. Simplify `this` using `[mul_add]`. Use the proof step `zero_mem' := by simpa using R.zero_mem`. Use the proof step `smul_mem' := fun c v hv => by`.

Use `R.mul_mem c.2 hv` as an intermediate fact. Simplify using `only [smul_eq_mul, Set.mem_setOf_eq, MulMemClass.coe_mul]`. Rewrite using `[mul_left_comm] }` and apply the resulting hypothesis. Establish `hI : I = ⊤`. Assume the negation of the conclusion as `hne`.

Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal I hne`. Take `⟨u, v, hv, huv⟩` from `h M hM.isPrime`. Use `hv (hle ?_)` and prove the remaining obligations. Use `show x * (v : Ω) ∈ R`. Rewrite using `[huv]`.

Conclude with `u.2`. Establish `h1 : (1 : R) ∈ I` using `hI ▸ Submodule.mem_top`. Establish `h2 : x * ((1 : R) : Ω) ∈ R` using `h1`. Simplify using `using h2`.
-/
theorem mem_of_loc {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) (x : Ω)
    (h : ∀ 𝔮 : Ideal R, 𝔮.IsPrime → ∃ u v : R, v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) : x ∈ R := by
  let I : Ideal R :=
    { carrier := {v | x * (v : Ω) ∈ R}
      add_mem' := fun {a b} ha hb => by
        have := R.add_mem ha hb
        simpa [mul_add] using this
      zero_mem' := by simpa using R.zero_mem
      smul_mem' := fun c v hv => by
        have := R.mul_mem c.2 hv
        simp only [smul_eq_mul, Set.mem_setOf_eq, MulMemClass.coe_mul]
        rwa [mul_left_comm] }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨u, v, hv, huv⟩ := h M hM.isPrime
    refine hv (hle ?_)
    show x * (v : Ω) ∈ R
    rw [huv]; exact u.2
  have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  have h2 : x * ((1 : R) : Ω) ∈ R := h1
  simpa using h2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `he`. Use `(Submodule.span_le.2 ?_ : M.htW L n ρ σ 𝔡 q ≤ M.htDual L n ρ σ q) he` and prove the remaining obligations. Introduce and unpack `e ⟨-, he⟩`. Establish `h1 : o • σ x • e ∈ M.htDual L n ρ σ q` using `(M.htDual L n ρ σ q).smul_mem ⟨o, ho⟩ (he x hx)`.

Rewrite `h1` using `[smul_smul, hox, one_smul]`. Conclude with `h1`. Introduce `he`. Use `Submodule.subset_span ⟨M.mem_eigSp_of_mem_htDual L n ρ σ he, fun d _ => ?_⟩` and prove the remaining obligations. Conclude with `(M.htDual L n ρ σ q).smul_mem ⟨σ d, hσ d⟩ he`.
-/
theorem mem_htW_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) (n : ℕ)
    {B : Type} [CommRing B] (ρ : B →+* Module.End Ω Li) (σ : B →+* Ω) (𝔡 : Ideal B) (q : Cpt ξ)
    (hσ : ∀ d, σ d ∈ regAt ξ q) (x : B) (hx : x ∈ 𝔡) (o : Ω) (ho : o ∈ regAt ξ q) (hox : o * σ x = 1) (e : Li) :
    e ∈ M.htW L n ρ σ 𝔡 q ↔ e ∈ M.htDual L n ρ σ q := by
  constructor
  · intro he
    refine (Submodule.span_le.2 ?_ : M.htW L n ρ σ 𝔡 q ≤ M.htDual L n ρ σ q) he
    rintro e ⟨-, he⟩
    have h1 : o • σ x • e ∈ M.htDual L n ρ σ q := (M.htDual L n ρ σ q).smul_mem ⟨o, ho⟩ (he x hx)
    rw [smul_smul, hox, one_smul] at h1
    exact h1
  · intro he
    refine Submodule.subset_span ⟨M.mem_eigSp_of_mem_htDual L n ρ σ he, fun d _ => ?_⟩
    exact (M.htDual L n ρ σ q).smul_mem ⟨σ d, hσ d⟩ he

/- English proof (translation)
Use `⟨fun h w hw => h w (Submodule.subset_span hw), fun h w hw => ?_⟩` and prove the remaining obligations. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact h x hx`. Consider the case `zero => simpa using R.zero_mem`. Consider the case `add x y _ _ hx hy => simpa using R.add_mem hx hy`.

Consider the case `smul c x _ hx => exact R.mul_mem c.2 hx`.
-/
theorem span_apply_iff {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] (R : Subring Ω)
    (T : Set (Module.Dual Ω V)) (e : V) :
    (∀ w ∈ Submodule.span R T, w e ∈ R) ↔ ∀ w ∈ T, w e ∈ R := by
  refine ⟨fun h w hw => h w (Submodule.subset_span hw), fun h w hw => ?_⟩
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simpa using R.zero_mem
  | add x y _ _ hx hy => simpa using R.add_mem hx hy
  | smul c x _ hx => exact R.mul_mem c.2 hx

end PositivityTheory.Xgn.SequenceCoordinates

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ _ p _ _ b hb A _ _ _ m _ _ O _ _ _ _ _ _ _ G c' _ P s hemb hdiff hCR hpr hloc a`. Establish `he : (∑ k, a k • b s k) ∈ eigSp 𝔐.ρ (𝔐.emb s)`. Establish `h` using `(hb s).2`. Unfold `HodgeCpt.Vgen at h`. Rewrite using `[← h]`.

Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Take `⟨x, hx, o, hox⟩` from `hdiff`. Establish `key : ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ((∑ k, a k • b s k) ∈ 𝔐.HT p s q ↔ ∀ u ∈ P.Dh.om', u (∑ k, a k • b s k) ∈ regAt 𝔐.ξ q)`. Introduce `q h1 h2`. Establish `hD : (∑ k, a k • b s k) ∈ 𝔐.HT p s q ↔ (∑ k, a k • b s k) ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q`.

Consider the cases of `s with`. Consider the case `inl τ`. Use `PositivityTheory.Xgn.SequenceCoordinates.mem_htW_iff 𝔐.M 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (.inl τ)) _ q (fun d => ?_) x hx _ (h2 o) hox _` and prove the remaining obligations. Take `⟨o', ho'⟩` from `hemb d`. Rewrite using `[← ho']`.

Conclude with `h2 o'`. Consider the case `inr τ => exact Iff.rfl`. Rewrite using `[hD, LieModel.mem_htDual_iff, and_iff_right he]`. Establish `hl : 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q = _` using `hloc q h1 h2`. Rewrite using `[hl, PositivityTheory.Xgn.SequenceCoordinates.span_apply_iff]`.

Both sides reduce to the same expression. Establish `hm : a ∈ coordLat O y (𝔐.HT p s) (b s) c' ↔ ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∑ k, a k • b s k ∈ 𝔐.HT p s q`. Simplify using `[coordLat, AddSubgroup.mem_iInf, Fintype.linearCombination_apply]`. Rewrite using `[hm]`. Prove the components needed by the constructor for the conclusion.

Introduce `h u hu`. Use `PositivityTheory.Xgn.SequenceCoordinates.mem_of_loc _ _ fun 𝔮 h𝔮 => ?_` and prove the remaining obligations. Take `⟨q, h1, h2, h3⟩` from `hpr 𝔮 h𝔮`. Conclude with `(h3 _).1 ((key q h1 h2).1 (h q h1 h2) u hu)`. Introduce `h q h1 h2`.

Conclude with `(key q h1 h2).2 fun u hu => hCR q h1 h2 _ (h u hu)`.
-/
theorem PositivityTheory.Xgn.sequence_coordinates_exist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), ∀ (s : CMType H ⊕ CMType H), (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = 𝔐.emb s a) → (∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * 𝔐.emb s x = 1) → (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) → (∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) → (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li))) → ∀ a : Fin (labelRk D s) → Ω, a ∈ coordLat O y (𝔐.HT p s) (b s) c' ↔ ∀ u ∈ P.Dh.om', u (∑ k, a k • b s k) ∈ CR O y c' := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ _ p _ _ b hb A _ _ _ m _ _ O _ _ _ _ _ _ _ G c' _ P s
    hemb hdiff hCR hpr hloc a
  have he : (∑ k, a k • b s k) ∈ eigSp 𝔐.ρ (𝔐.emb s) := by
    have h := (hb s).2
    unfold HodgeCpt.Vgen at h
    rw [← h]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨x, hx, o, hox⟩ := hdiff
  have key : ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) →
      ((∑ k, a k • b s k) ∈ 𝔐.HT p s q ↔ ∀ u ∈ P.Dh.om', u (∑ k, a k • b s k) ∈ regAt 𝔐.ξ q) := by
    intro q h1 h2
    have hD : (∑ k, a k • b s k) ∈ 𝔐.HT p s q ↔
        (∑ k, a k • b s k) ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q := by
      cases s with
      | inl τ =>
        refine PositivityTheory.Xgn.SequenceCoordinates.mem_htW_iff 𝔐.M 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (.inl τ)) _ q
          (fun d => ?_) x hx _ (h2 o) hox _
        obtain ⟨o', ho'⟩ := hemb d
        rw [← ho']; exact h2 o'
      | inr τ => exact Iff.rfl
    rw [hD, LieModel.mem_htDual_iff, and_iff_right he]
    have hl : 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q = _ := hloc q h1 h2
    rw [hl, PositivityTheory.Xgn.SequenceCoordinates.span_apply_iff]
    rfl
  have hm : a ∈ coordLat O y (𝔐.HT p s) (b s) c' ↔ ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q →
      (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∑ k, a k • b s k ∈ 𝔐.HT p s q := by
    simp [coordLat, AddSubgroup.mem_iInf, Fintype.linearCombination_apply]
  rw [hm]
  constructor
  · intro h u hu
    refine PositivityTheory.Xgn.SequenceCoordinates.mem_of_loc _ _ fun 𝔮 h𝔮 => ?_
    obtain ⟨q, h1, h2, h3⟩ := hpr 𝔮 h𝔮
    exact (h3 _).1 ((key q h1 h2).1 (h q h1 h2) u hu)
  · intro h q h1 h2
    exact (key q h1 h2).2 fun u hu => hCR q h1 h2 _ (h u hu)
