import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.DiagLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.LowLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `i j hij`. Establish `hB : Matrix.BlockTriangular (X * Y) id` using `Matrix.BlockTriangular.mul (fun a b h => hX a b h) (fun a b h => hY a b h)`. Conclude with `hB hij`.
-/
private theorem isUp_mul {A : Type} [CommRing A] {X Y : M4 A} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j hij
  have hB : Matrix.BlockTriangular (X * Y) id :=
    Matrix.BlockTriangular.mul (fun a b h => hX a b h) (fun a b h => hY a b h)
  exact hB hij

/- English proof (translation)
Introduce `N`. Establish `hpi : IsLocallyConstant fun g => fun k m => Ideal.Quotient.mk (I ^ N) (f g k m)`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `g0`. Establish `hev : ∀ᶠ g in nhds g0, ∀ k m, Ideal.Quotient.mk (I ^ N) (f g k m) = Ideal.Quotient.mk (I ^ N) (f g0 k m)`.

Simplify using `only [Filter.eventually_all]`. Introduce `k m`. Conclude with `(h k m N).eventually_eq g0`. Use `filter_upwards [hev] with g hg`. Use function extensionality and compare the values at `k m`.

Conclude with `hg k m`. Use `hpi.comp (fun M : Fin 4 → Fin 4 → A ⧸ I ^ N => ∑ m, ∑ k, Ideal.Quotient.mk (I ^ N) (x i k) * M k m * Ideal.Quotient.mk (I ^ N) (y m j)) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using `[Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]`.
-/
private theorem cont_conj {Γ A : Type} [TopologicalSpace Γ] [CommRing A] (I : Ideal A) (f : Γ → M4 A) (x y : M4 A)
    (h : ∀ i j, AdicCont I fun g => f g i j) (i j : Fin 4) : AdicCont I fun g => (x * f g * y) i j := by
  intro N
  have hpi : IsLocallyConstant fun g => fun k m => Ideal.Quotient.mk (I ^ N) (f g k m) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have hev : ∀ᶠ g in nhds g0, ∀ k m,
        Ideal.Quotient.mk (I ^ N) (f g k m) = Ideal.Quotient.mk (I ^ N) (f g0 k m) := by
      simp only [Filter.eventually_all]
      intro k m
      exact (h k m N).eventually_eq g0
    filter_upwards [hev] with g hg
    funext k m
    exact hg k m
  convert hpi.comp (fun M : Fin 4 → Fin 4 → A ⧸ I ^ N =>
    ∑ m, ∑ k, Ideal.Quotient.mk (I ^ N) (x i k) * M k m * Ideal.Quotient.mk (I ^ N) (y m j)) using 1
  funext g
  simp [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]

/- English proof (translation)
Introduce `O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hStd hMu Γb _ _ _ _ π hQuo c hRes R _ _ _ P hDef ν r hν hr A _ _ _ p hsurj hker hW`. Take `⟨r', n', hWP, hcont, hr', hn'⟩` from `hW`. Establish `hPair` using `hDef.1.pair`. Establish `hmapmul : ∀ X Y : M4 A, Matrix.map (X * Y) p = Matrix.map X p * Matrix.map Y p`. Introduce `X Y`.

Conclude with `Matrix.map_mul (f := (p : A →+* R))`. Establish `hrπ : ∀ g, Matrix.map (r' (π g)) p = P.r g`. Introduce `g`. Rewrite using `[hr', ← hr]`. Both sides reduce to the same expression.

Establish `hresR : ∀ g i j, res Λ R (P.r g i j) = c.r g i j`. Introduce `g i j`. Rewrite using `[← hDef.1.red, PD.map_r]`. Both sides reduce to the same expression. Establish `hXunit : ∀ i j, i ≠ j → IsUnit (r' (π Φ.g0) i i - r' (π Φ.g0) j j)`.

Introduce `i j hij`. Establish `hd` using `hStd.ok.dist i j hij`. Establish `he : res Λ A (r' (π Φ.g0) i i - r' (π Φ.g0) j j) = (residue Λ).comp a (Φ.χ i Φ.g0) - (residue Λ).comp a (Φ.χ j Φ.g0)`. Rewrite using `[← res_map p, map_sub]`. Establish `hi : p (r' (π Φ.g0) i i) = P.r Φ.g0 i i`.

Rewrite using `[← hrπ]`. Both sides reduce to the same expression. Establish `hj : p (r' (π Φ.g0) j j) = P.r Φ.g0 j j`. Rewrite using `[← hrπ]`. Both sides reduce to the same expression.

Rewrite using `[hi, hj, map_sub, hresR, hresR, hRes.res.diag, hRes.res.diag]`. Assume the negation of the conclusion as `hnu`. Establish `hm : r' (π Φ.g0) i i - r' (π Φ.g0) j j ∈ maximalIdeal A` using `(mem_maximalIdeal _).2 hnu`. Rewrite `hm` using `[← res_eq_zero_iff Λ A, he]`. Rewrite `hd` using `[hm]`.

Conclude with `not_isUnit_zero hd`. Take `⟨u, hu1, hup, hudiag⟩` from `X1.diagLift p hsurj hker (algebraMap Λ A (ν (π Φ.g0))) (r' (π Φ.g0)) ((ν (π Φ.g0)).isUnit.map (algebraMap Λ A)) (hWP.mult (π Φ.g0)) (by rw [hrπ]; exact hPair.nrm) hXunit`. Establish `huadj : adj u * u = 1`. Establish `h` using `hu1`. Unfold `IsGSp at h`.

Simplify using `using h`. Establish `hu_adj : u * adj u = 1` using `mul_eq_one_comm.1 huadj`. Establish `hadjGSp : IsGSp 1 (adj u)`. Unfold `IsGSp`. Rewrite using `[(grp A).2.1 u, hu_adj, one_smul]`.

Establish `hmapadj : Matrix.map (adj u) p = 1`. Establish `h` using `(grp A).2.2.2.2.2.1 R (p : A →+* R) u`. Establish `h' : Matrix.map (adj u) p = adj (Matrix.map u p)` using `h.symm`. Rewrite using `[h', hup, (grp R).2.2.2.2.1]`. Establish `hlow : ∀ v, ∃ m b, IsLow m ∧ IsGSp 1 b ∧ IsUp b ∧ IsUp (adj b) ∧ Matrix.map m p = Matrix.map (adj u * n' v) p ∧ m = adj u * n' v * b`.

Introduce `v`. Use `X1.lowLift p hsurj hker (adj u * n' v) ?_ ?_` and prove the remaining obligations. Establish `h` using `(grp A).2.2.2.2.2.2.2.1 1 1 (adj u) (n' v) hadjGSp (hWP.sp v)`. Simplify using `using h`. Rewrite using `[hmapmul, hmapadj, one_mul, hn']`.

Conclude with `hPair.low v`. Use `choose m b hm using hlow`. Set `r'' : Γ →* M4 A` to `{ toFun := fun g => adj u * r' (π g) * u map_one' := by simp [huadj] map_mul' := by`. Introduce `x y`. Simplify using `only [map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Set `P' : PD Φ.ι Γ A` to `⟨r'', m⟩`. Establish `hPP' : P'.map (p : A →+* R) = P`. Apply `PD.ext` to reduce the goal to its premises. Apply `MonoidHom.ext` to reduce the goal to its premises.

Introduce `g`. Rewrite using `[PD.map_r]`. Express the relevant statement in the definitionally equal form `Matrix.map (adj u * r' (π g) * u) p = P.r g`. Rewrite using `[hmapmul, hmapmul, hmapadj, hup, hrπ, one_mul, mul_one]`. Use function extensionality and compare the values at `v`.

Express the relevant statement in the definitionally equal form `Matrix.map (m v) p = P.n v`. Rewrite using `[(hm v).2.2.2.2.1, hmapmul, hmapadj, one_mul, hn']`. Establish `hLift : Φ.Lifts a c P'`. Use `⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `g`.

Express the relevant statement in the definitionally equal form `IsGSp (algebraMap Λ A (a (Φ.ν g))) (adj u * r' (π g) * u)`. Rewrite using `[← hν g]`. Establish `h1 : IsGSp (algebraMap Λ A (ν (π g))) (r' (π g))` using `hWP.mult (π g)`. Establish `h2` using `(grp A).2.2.2.2.2.2.2.1 _ _ _ _ ((grp A).2.2.2.2.2.2.2.1 _ _ _ _ hadjGSp h1) hu1`. Simplify using `using h2`.

Introduce `g hg`. Establish `hπg : π g = 1`. Rewrite using `[← MonoidHom.mem_ker, hQuo.ker]`. Conclude with `Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hg)`. Express the relevant statement in the definitionally equal form `adj u * r' (π g) * u = 1`.

Rewrite using `[hπg, map_one, mul_one, huadj]`. Conclude with `hudiag`. Introduce `v`. Conclude with `(hm v).1`. Introduce `v s hs`.

Express the relevant statement in the definitionally equal form `IsUp (adj (m v) * (adj u * r' (π s) * u) * m v)`. Establish `hfl : IsUp (adj (n' v) * r' (π s) * n' v)` using `hWP.flag v ⟨s, hs⟩`. Establish `key : adj (m v) * (adj u * r' (π s) * u) * m v = adj (b v) * (adj (n' v) * r' (π s) * n' v) * b v`. Rewrite using `[(hm v).2.2.2.2.2]`. Simplify using `only [(grp A).1, (grp A).2.1]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hu_adj]`. Use `noncomm_ring`. Rewrite using `[key]`. Conclude with `isUp_mul (isUp_mul (hm v).2.2.2.1 hfl) (hm v).2.2.1`.

Introduce `v s hs`. Rewrite `hs` using `[hMu v]`. Conclude with `absurd hs (Set.notMem_empty _)`. Introduce `i j`. Conclude with `cont_conj (maximalIdeal A) (fun g => r' (π g)) (adj u) u (fun i j N => (hcont i j N).comp_continuous hQuo.cont) i j`.

Establish `hres : (res Λ A : A →+* ResidueField Λ) = (res Λ R : R →+* ResidueField Λ).comp (p : A →+* R)`. Use extensionality with `x`. Conclude with `(res_map p x).symm`. Rewrite using `[hres, ← PD.map_map, hPP', hDef.1.red]`. Take `⟨f, hf, -⟩` from `hDef.2 A P' hLift`.

Take `⟨g0, -, huniq⟩` from `hDef.2 R P hDef.1`. Use `⟨f, ?_⟩` and prove the remaining obligations. Establish `e1 : p.comp f = g0`. Apply `huniq` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `P.map ((p : A →+* R).comp (f : R →+* A)) = P`.

Rewrite using `[← PD.map_map, hf, hPP']`. Establish `e2 : AlgHom.id Λ R = g0`. Apply `huniq` to reduce the goal to its premises. Apply `PD.ext` to reduce the goal to its premises. Apply `MonoidHom.ext` to reduce the goal to its premises.

Introduce `g`. Rewrite using `[PD.map_r]`. Use extensionality with `i j`. Both sides reduce to the same expression. Use function extensionality and compare the values at `v`.

Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[e1, e2]`.
-/
theorem UpperTheory.V.Ws.X1.sect :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → (∀ v, Φ.Mu v = ∅) → ∀ {Γb : Type} [Group Γb] [TopologicalSpace Γb] [IsTopologicalGroup Γb] [T2Space Γb] (π : Γ →* Γb), Φ.Quo π → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R), Φ.IsDef a c P → ∀ (ν : Γb →* Λˣ) (r : Γb →* M4 R), (∀ g, (ν (π g) : Λ) = a (Φ.ν g)) → r.comp π = P.r → ∀ (A : Type) [CommRing A] [Algebra Λ A] [IsCO Λ A] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → WLift (Φ.loc π) ν r P.n p → ∃ s : R →ₐ[Λ] A, p.comp s = AlgHom.id Λ R := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hStd hMu Γb _ _ _ _ π hQuo c hRes R _ _ _ P hDef ν r hν hr
    A _ _ _ p hsurj hker hW
  obtain ⟨r', n', hWP, hcont, hr', hn'⟩ := hW
  have hPair := hDef.1.pair
  have hmapmul : ∀ X Y : M4 A, Matrix.map (X * Y) p = Matrix.map X p * Matrix.map Y p := by
    intro X Y
    exact Matrix.map_mul (f := (p : A →+* R))
  have hrπ : ∀ g, Matrix.map (r' (π g)) p = P.r g := by
    intro g
    rw [hr', ← hr]
    rfl
  have hresR : ∀ g i j, res Λ R (P.r g i j) = c.r g i j := by
    intro g i j
    rw [← hDef.1.red, PD.map_r]
    rfl
  have hXunit : ∀ i j, i ≠ j →
      IsUnit (r' (π Φ.g0) i i - r' (π Φ.g0) j j) := by
    intro i j hij
    have hd := hStd.ok.dist i j hij
    have he : res Λ A (r' (π Φ.g0) i i - r' (π Φ.g0) j j) =
        (residue Λ).comp a (Φ.χ i Φ.g0) - (residue Λ).comp a (Φ.χ j Φ.g0) := by
      rw [← res_map p, map_sub]
      have hi : p (r' (π Φ.g0) i i) = P.r Φ.g0 i i := by
        rw [← hrπ]
        rfl
      have hj : p (r' (π Φ.g0) j j) = P.r Φ.g0 j j := by
        rw [← hrπ]
        rfl
      rw [hi, hj, map_sub, hresR, hresR, hRes.res.diag, hRes.res.diag]
    by_contra hnu
    have hm : r' (π Φ.g0) i i - r' (π Φ.g0) j j ∈ maximalIdeal A := (mem_maximalIdeal _).2 hnu
    rw [← res_eq_zero_iff Λ A, he] at hm
    rw [hm] at hd
    exact not_isUnit_zero hd
  obtain ⟨u, hu1, hup, hudiag⟩ := X1.diagLift p hsurj hker (algebraMap Λ A (ν (π Φ.g0)))
    (r' (π Φ.g0)) ((ν (π Φ.g0)).isUnit.map (algebraMap Λ A)) (hWP.mult (π Φ.g0))
    (by rw [hrπ]; exact hPair.nrm) hXunit
  have huadj : adj u * u = 1 := by
    have h := hu1
    unfold IsGSp at h
    simpa using h
  have hu_adj : u * adj u = 1 := mul_eq_one_comm.1 huadj
  have hadjGSp : IsGSp 1 (adj u) := by
    unfold IsGSp
    rw [(grp A).2.1 u, hu_adj, one_smul]
  have hmapadj : Matrix.map (adj u) p = 1 := by
    have h := (grp A).2.2.2.2.2.1 R (p : A →+* R) u
    have h' : Matrix.map (adj u) p = adj (Matrix.map u p) := h.symm
    rw [h', hup, (grp R).2.2.2.2.1]
  have hlow : ∀ v, ∃ m b, IsLow m ∧ IsGSp 1 b ∧ IsUp b ∧ IsUp (adj b) ∧
      Matrix.map m p = Matrix.map (adj u * n' v) p ∧ m = adj u * n' v * b := by
    intro v
    refine X1.lowLift p hsurj hker (adj u * n' v) ?_ ?_
    · have h := (grp A).2.2.2.2.2.2.2.1 1 1 (adj u) (n' v) hadjGSp (hWP.sp v)
      simpa using h
    · rw [hmapmul, hmapadj, one_mul, hn']
      exact hPair.low v
  choose m b hm using hlow
  let r'' : Γ →* M4 A :=
    { toFun := fun g => adj u * r' (π g) * u
      map_one' := by simp [huadj]
      map_mul' := by
        intro x y
        simp only [map_mul]
        calc adj u * (r' (π x) * r' (π y)) * u
            = adj u * r' (π x) * (u * adj u) * r' (π y) * u := by rw [hu_adj]; noncomm_ring
          _ = adj u * r' (π x) * u * (adj u * r' (π y) * u) := by noncomm_ring }
  let P' : PD Φ.ι Γ A := ⟨r'', m⟩
  have hPP' : P'.map (p : A →+* R) = P := by
    apply PD.ext
    · apply MonoidHom.ext
      intro g
      rw [PD.map_r]
      change Matrix.map (adj u * r' (π g) * u) p = P.r g
      rw [hmapmul, hmapmul, hmapadj, hup, hrπ, one_mul, mul_one]
    · funext v
      change Matrix.map (m v) p = P.n v
      rw [(hm v).2.2.2.2.1, hmapmul, hmapadj, one_mul, hn']
  have hLift : Φ.Lifts a c P' := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro g
      change IsGSp (algebraMap Λ A (a (Φ.ν g))) (adj u * r' (π g) * u)
      rw [← hν g]
      have h1 : IsGSp (algebraMap Λ A (ν (π g))) (r' (π g)) := hWP.mult (π g)
      have h2 := (grp A).2.2.2.2.2.2.2.1 _ _ _ _ ((grp A).2.2.2.2.2.2.2.1 _ _ _ _ hadjGSp h1) hu1
      simpa using h2
    · intro g hg
      have hπg : π g = 1 := by
        rw [← MonoidHom.mem_ker, hQuo.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hg)
      change adj u * r' (π g) * u = 1
      rw [hπg, map_one, mul_one, huadj]
    · exact hudiag
    · intro v
      exact (hm v).1
    · intro v s hs
      change IsUp (adj (m v) * (adj u * r' (π s) * u) * m v)
      have hfl : IsUp (adj (n' v) * r' (π s) * n' v) := hWP.flag v ⟨s, hs⟩
      have key : adj (m v) * (adj u * r' (π s) * u) * m v =
          adj (b v) * (adj (n' v) * r' (π s) * n' v) * b v := by
        rw [(hm v).2.2.2.2.2]
        simp only [(grp A).1, (grp A).2.1]
        calc adj (b v) * (adj (n' v) * u) * (adj u * r' (π s) * u) * (adj u * n' v * b v)
            = adj (b v) * adj (n' v) * (u * adj u) * r' (π s) * (u * adj u) * n' v * b v := by
              noncomm_ring
          _ = adj (b v) * (adj (n' v) * r' (π s) * n' v) * b v := by
              rw [hu_adj]
              noncomm_ring
      rw [key]
      exact isUp_mul (isUp_mul (hm v).2.2.2.1 hfl) (hm v).2.2.1
    · intro v s hs
      rw [hMu v] at hs
      exact absurd hs (Set.notMem_empty _)
    · intro i j
      exact cont_conj (maximalIdeal A) (fun g => r' (π g)) (adj u) u
        (fun i j N => (hcont i j N).comp_continuous hQuo.cont) i j
    · have hres : (res Λ A : A →+* ResidueField Λ) = (res Λ R : R →+* ResidueField Λ).comp (p : A →+* R) := by
        ext x
        exact (res_map p x).symm
      rw [hres, ← PD.map_map, hPP', hDef.1.red]
  obtain ⟨f, hf, -⟩ := hDef.2 A P' hLift
  obtain ⟨g0, -, huniq⟩ := hDef.2 R P hDef.1
  refine ⟨f, ?_⟩
  have e1 : p.comp f = g0 := by
    apply huniq
    change P.map ((p : A →+* R).comp (f : R →+* A)) = P
    rw [← PD.map_map, hf, hPP']
  have e2 : AlgHom.id Λ R = g0 := by
    apply huniq
    apply PD.ext
    · apply MonoidHom.ext
      intro g
      rw [PD.map_r]
      ext i j
      rfl
    · funext v
      ext i j
      rfl
  rw [e1, e2]
