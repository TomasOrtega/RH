import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke

/- English proof (translation)
Introduce `p _ D R _ b g k N hk hN hkp hNp S s o`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `haveI := D.finLa`. Set `K : Submodule ℤ D.La` to `LinearMap.range ((k : ℤ) • LinearMap.id)`. Use `haveI : Finite (D.La ⧸ K) := by`.

Apply `Module.finite_of_fg_torsion` to reduce the goal to its premises. Introduce `q`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective K q`. Use `⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩` and prove the remaining obligations. Use `show (k : ℤ) • (Submodule.Quotient.mk y : D.La ⧸ K) = 0`.

Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨y, by simp⟩`. Set `σ` to `Function.surjInv (Submodule.Quotient.mk_surjective K)`. Use `Finite.of_surjective (fun q : D.La ⧸ K => (⟨o.eta (N • g (σ q)), mem_heckeSub o g N _⟩ : heckeSub o g N)) ?_` and prove the remaining obligations. Introduce and unpack `⟨h, x, rfl⟩`.

Use `⟨Submodule.Quotient.mk x, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `e : Submodule.Quotient.mk (σ (Submodule.Quotient.mk x)) = (Submodule.Quotient.mk x : D.La ⧸ K)` using `Function.surjInv_eq _ _`. Rewrite `e` using `[Submodule.Quotient.eq]`. Take `⟨z, hz⟩` from `e`. Establish `hz' : σ (Submodule.Quotient.mk x) = x + k • z`.

Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul] at hz`. Rewrite using `[hz]`. Normalize the expressions using the abelian group laws. Use `show o.eta (N • g (σ (Submodule.Quotient.mk x))) = o.eta (N • g x)`. Rewrite using `[hz', map_add, map_nsmul, smul_add, smul_smul, o.eta_add, o.eta_ker, _root_.mul_one]`.

Introduce `κ _ _ x h hh h1`. Take `⟨x0, rfl⟩` from `hh`. Establish `hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom` using `(Spec.map_preimage _).symm`. Take `⟨I, hI⟩` from `o.geom κ x _ hβ`. Establish `h2 : I.ev (N * k) (N • g x0) = 1` using `by rw [← hI]; exact h1`.

Take `⟨y, hy⟩` from `(I.ker (N * k) (Nat.mul_pos hN hk) (Nat.Coprime.mul hNp hkp) _).1 h2`. Rewrite using `[hy, o.eta_ker]`.
-/
theorem heckeSub_finite_free : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (k N : ℕ), 0 < k → 0 < N → k.Coprime p → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), Finite (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ o.A), h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N → toUnit (Over.mk x) ≫ h = 1 → h = 1 := by
  intro p _ D R _ b g k N hk hN hkp hNp S s o
  refine ⟨?_, ?_⟩
  · haveI := D.finLa
    let K : Submodule ℤ D.La := LinearMap.range ((k : ℤ) • LinearMap.id)
    haveI : Finite (D.La ⧸ K) := by
      apply Module.finite_of_fg_torsion
      intro q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K q
      refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
      show (k : ℤ) • (Submodule.Quotient.mk y : D.La ⧸ K) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨y, by simp⟩
    let σ := Function.surjInv (Submodule.Quotient.mk_surjective K)
    refine Finite.of_surjective (fun q : D.La ⧸ K => (⟨o.eta (N • g (σ q)), mem_heckeSub o g N _⟩ : heckeSub o g N)) ?_
    rintro ⟨h, x, rfl⟩
    refine ⟨Submodule.Quotient.mk x, Subtype.ext ?_⟩
    have e : Submodule.Quotient.mk (σ (Submodule.Quotient.mk x)) = (Submodule.Quotient.mk x : D.La ⧸ K) :=
      Function.surjInv_eq _ _
    rw [Submodule.Quotient.eq] at e
    obtain ⟨z, hz⟩ := e
    have hz' : σ (Submodule.Quotient.mk x) = x + k • z := by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul] at hz
      rw [hz]; abel
    show o.eta (N • g (σ (Submodule.Quotient.mk x))) = o.eta (N • g x)
    rw [hz', map_add, map_nsmul, smul_add, smul_smul, o.eta_add, o.eta_ker, _root_.mul_one]
  · intro κ _ _ x h hh h1
    obtain ⟨x0, rfl⟩ := hh
    have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
    obtain ⟨I, hI⟩ := o.geom κ x _ hβ
    have h2 : I.ev (N * k) (N • g x0) = 1 := by rw [← hI]; exact h1
    obtain ⟨y, hy⟩ := (I.ker (N * k) (Nat.mul_pos hN hk) (Nat.Coprime.mul hNp hkp) _).1 h2
    rw [hy, o.eta_ker]

end GlobalTheory.UPel.HT.Hecke
