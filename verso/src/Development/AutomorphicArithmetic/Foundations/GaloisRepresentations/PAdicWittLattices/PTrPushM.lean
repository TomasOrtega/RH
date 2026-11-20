import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Introduce `hF hSB hSC hMS hInj B R _ T hT Y P Z p q r κ s d m hκ hs hd hm tr tr' htr htr' x`. Use `haveI : IsFinite s := hd.1`. Use `haveI : Etale s := hd.2.1`. Use `haveI : IsFinite κ := hm.1`. Use `haveI : Etale κ := hm.2.1`.

Take `⟨W1, c1, e1, he1, hc1, hτ0⟩` from `hMS 1 (fun _ => P) (fun _ => s) (fun _ => d) (fun _ => hd)`. Take `⟨τ, hτ⟩ : ∃ τ : Fin d → (W1 ⟶ P), Splits s c1 τ` from `hτ0 0`. Establish `hPb : ∀ i : Fin d, FEt (pullback.snd κ (τ i)) m` using `fun i => hF.1 (pullback.fst κ (τ i)) (pullback.snd κ (τ i)) κ (τ i) m (IsPullback.of_hasPullback κ (τ i)) hm`. Take `⟨W2, c2, e2, he2, hc2, hρ0⟩` from `hMS d (fun i => pullback κ (τ i)) (fun i => pullback.snd κ (τ i)) (fun _ => m) hPb`. Establish `hρ1 : ∀ i : Fin d, ∃ ρ : Fin m → (W2 ⟶ pullback κ (τ i)), Splits (pullback.snd κ (τ i)) c2 ρ` using `hρ0`.

Use `choose ρ hρ using hρ1`. Establish `key : ∀ i j, (ρ i j ≫ pullback.fst κ (τ i)) ≫ κ = c2 ≫ τ i` using `fun i j => by`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, (hρ i).1 j]`. Establish `hsκ : ∀ i, Splits κ (c2 ≫ τ i) (fun j => ρ i j ≫ pullback.fst κ (τ i))` using `fun i => (hSB.2 (pullback.fst κ (τ i)) (pullback.snd κ (τ i)) κ (τ i) (IsPullback.of_hasPullback κ (τ i)) c2 (Fin m) (ρ i) (hρ i).1).1 (hρ i)`. Establish `hss : Splits s (c2 ≫ c1) (fun i => c2 ≫ τ i)` using `hSB.1 s c1 (Fin d) τ c2 hτ`.

Establish `hcomp` using `hSC κ s (c2 ≫ c1) (Fin d) (Fin m) (fun i => c2 ≫ τ i) (fun i j => ρ i j ≫ pullback.fst κ (τ i)) hss hsκ`. Establish `hfc : FEt (c2 ≫ c1) (e1 * e2)` using `hF.2.1 c2 c1 e1 e2 hc2 hc1`. Establish `hστ : ∀ i, (c2 ≫ τ i) ≫ q = (c2 ≫ c1) ≫ p` using `fun i => by`. Rewrite using `[← hs]`. Simplify using `only [Category.assoc]`.

Rewrite using `[← Category.assoc (τ i) s p, hτ.1 i]`. Establish `hσ' : ∀ y : Fin d × Fin m, (ρ y.1 y.2 ≫ pullback.fst κ (τ y.1)) ≫ r = (c2 ≫ c1) ≫ p` using `fun y => by`. Rewrite using `[← hκ, ← Category.assoc, key]`. Conclude with `hστ y.1`. Establish `move : ∀ (f : W2 ⟶ Y) (g : W2 ⟶ P) (hf : f ≫ r = (c2 ≫ c1) ≫ p) (hg : g ≫ q = (c2 ≫ c1) ≫ p), f ≫ κ = g → T.pull f hf (T.pull κ hκ x) = T.pull g hg x`.

Introduce `f g hf hg e`. Substitute `e` using the available equality. Conclude with `(T.pull_comp f κ hf hκ hg x).symm`. Apply `hInj T hT p ((c2 ≫ c1) ≫ p) (c2 ≫ c1) rfl (e1 * e2) (Nat.mul_pos he1 he2) hfc` to reduce the goal to its premises. Rewrite using `[htr' W2 _ (c2 ≫ c1) rfl (Fin d × Fin m) (fun y => ρ y.1 y.2 ≫ pullback.fst κ (τ y.1)) hσ' hcomp]`.

Rewrite using `[map_smul, htr W2 _ (c2 ≫ c1) rfl (Fin d) (fun i => c2 ≫ τ i) hστ hss]`. Rewrite using `[Fintype.sum_prod_type, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl fun j _ => move _ _ (hσ' (i, j)) (hστ i) (key i j)]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]`.

Conclude with `(Nat.cast_smul_eq_nsmul R m _).symm`.
-/
theorem UpperTheory.Gal.G3.pTrPushM :
    FEtBasic → SplitsBasic → SplitsComp → MultiSplit → FEtInj.{u} → TrPushM.{u} := by
  intro hF hSB hSC hMS hInj B R _ T hT Y P Z p q r κ s d m hκ hs hd hm tr tr' htr htr' x
  haveI : IsFinite s := hd.1
  haveI : Etale s := hd.2.1
  haveI : IsFinite κ := hm.1
  haveI : Etale κ := hm.2.1
  obtain ⟨W1, c1, e1, he1, hc1, hτ0⟩ := hMS 1 (fun _ => P) (fun _ => s) (fun _ => d) (fun _ => hd)
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin d → (W1 ⟶ P), Splits s c1 τ := hτ0 0
  have hPb : ∀ i : Fin d, FEt (pullback.snd κ (τ i)) m := fun i =>
    hF.1 (pullback.fst κ (τ i)) (pullback.snd κ (τ i)) κ (τ i) m
      (IsPullback.of_hasPullback κ (τ i)) hm
  obtain ⟨W2, c2, e2, he2, hc2, hρ0⟩ :=
    hMS d (fun i => pullback κ (τ i)) (fun i => pullback.snd κ (τ i)) (fun _ => m) hPb
  have hρ1 : ∀ i : Fin d, ∃ ρ : Fin m → (W2 ⟶ pullback κ (τ i)),
      Splits (pullback.snd κ (τ i)) c2 ρ := hρ0
  choose ρ hρ using hρ1
  have key : ∀ i j, (ρ i j ≫ pullback.fst κ (τ i)) ≫ κ = c2 ≫ τ i := fun i j => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, (hρ i).1 j]
  have hsκ : ∀ i, Splits κ (c2 ≫ τ i) (fun j => ρ i j ≫ pullback.fst κ (τ i)) := fun i =>
    (hSB.2 (pullback.fst κ (τ i)) (pullback.snd κ (τ i)) κ (τ i)
      (IsPullback.of_hasPullback κ (τ i)) c2 (Fin m) (ρ i) (hρ i).1).1 (hρ i)
  have hss : Splits s (c2 ≫ c1) (fun i => c2 ≫ τ i) := hSB.1 s c1 (Fin d) τ c2 hτ
  have hcomp := hSC κ s (c2 ≫ c1) (Fin d) (Fin m) (fun i => c2 ≫ τ i)
    (fun i j => ρ i j ≫ pullback.fst κ (τ i)) hss hsκ
  have hfc : FEt (c2 ≫ c1) (e1 * e2) := hF.2.1 c2 c1 e1 e2 hc2 hc1
  have hστ : ∀ i, (c2 ≫ τ i) ≫ q = (c2 ≫ c1) ≫ p := fun i => by
    rw [← hs]
    simp only [Category.assoc]
    rw [← Category.assoc (τ i) s p, hτ.1 i]
  have hσ' : ∀ y : Fin d × Fin m, (ρ y.1 y.2 ≫ pullback.fst κ (τ y.1)) ≫ r = (c2 ≫ c1) ≫ p :=
    fun y => by
      rw [← hκ, ← Category.assoc, key]
      exact hστ y.1
  have move : ∀ (f : W2 ⟶ Y) (g : W2 ⟶ P) (hf : f ≫ r = (c2 ≫ c1) ≫ p)
      (hg : g ≫ q = (c2 ≫ c1) ≫ p), f ≫ κ = g → T.pull f hf (T.pull κ hκ x) = T.pull g hg x := by
    intro f g hf hg e
    subst e
    exact (T.pull_comp f κ hf hκ hg x).symm
  apply hInj T hT p ((c2 ≫ c1) ≫ p) (c2 ≫ c1) rfl (e1 * e2) (Nat.mul_pos he1 he2) hfc
  rw [htr' W2 _ (c2 ≫ c1) rfl (Fin d × Fin m) (fun y => ρ y.1 y.2 ≫ pullback.fst κ (τ y.1)) hσ' hcomp]
  rw [map_smul, htr W2 _ (c2 ≫ c1) rfl (Fin d) (fun i => c2 ≫ τ i) hστ hss]
  rw [Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl fun j _ => move _ _ (hσ' (i, j)) (hστ i) (key i j)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact (Nat.cast_smul_eq_nsmul R m _).symm
