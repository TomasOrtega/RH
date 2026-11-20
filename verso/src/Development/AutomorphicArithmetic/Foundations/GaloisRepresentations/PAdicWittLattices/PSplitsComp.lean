import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Introduce `hS hP Y P Z W κ s _ _ _ _ c I J _ _ τ σ hτ hσ`. Establish `hτc : ∀ i, τ i ≫ s = c` using `hτ.1`. Establish `hσc : ∀ i j, σ i j ≫ κ = τ i` using `fun i => (hσ i).1`. Use `hS (κ ≫ s) c (I × J) (fun x => σ x.1 x.2) (fun x => by rw [← Category.assoc, hσc, hτc]) ?_` and prove the remaining obligations. Introduce `Ω _ _ x y hy`.

Take `⟨i, hi, hiu⟩` from `hP s c I τ hτ Ω x (y ≫ κ) (by simpa using hy)`. Take `⟨j, hj, hju⟩` from `hP κ (τ i) J (σ i) (hσ i) Ω x y hi.symm`. Use `⟨(i, j), hj, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨i', j'⟩ h'`. Establish `h'' : x ≫ σ i' j' = y` using `h'`.

Establish `hi' : i' = i` using `hiu i' (by show x ≫ τ i' = y ≫ κ`. Rewrite using `[← hσc i' j', ← Category.assoc, h''])`. Substitute `hi'` using the available equality. Establish `hj' : j' = j` using `hju j' h''`. Substitute `hj'` using the available equality.

Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.G3.pSplitsComp :
    SplitsPts → PtsOfSplits → SplitsComp := by
  intro hS hP Y P Z W κ s _ _ _ _ c I J _ _ τ σ hτ hσ
  have hτc : ∀ i, τ i ≫ s = c := hτ.1
  have hσc : ∀ i j, σ i j ≫ κ = τ i := fun i => (hσ i).1
  refine hS (κ ≫ s) c (I × J) (fun x => σ x.1 x.2)
    (fun x => by rw [← Category.assoc, hσc, hτc]) ?_
  intro Ω _ _ x y hy
  obtain ⟨i, hi, hiu⟩ := hP s c I τ hτ Ω x (y ≫ κ) (by simpa using hy)
  obtain ⟨j, hj, hju⟩ := hP κ (τ i) J (σ i) (hσ i) Ω x y hi.symm
  refine ⟨(i, j), hj, ?_⟩
  rintro ⟨i', j'⟩ h'
  have h'' : x ≫ σ i' j' = y := h'
  have hi' : i' = i := hiu i' (by
    show x ≫ τ i' = y ≫ κ
    rw [← hσc i' j', ← Category.assoc, h''])
  subst hi'
  have hj' : j' = j := hju j' h''
  subst hj'
  rfl
