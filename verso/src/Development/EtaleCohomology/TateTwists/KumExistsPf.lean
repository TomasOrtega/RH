import Development.EtaleCohomology.TateTwists.EtaleKummerClassSpecificationOfExistenceNaturali

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def L_kumT_ex : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

def L_prim_loc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def L_sec_glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

def L_sch_cls : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n k : ℤ), m + 1 = n → n + 1 = k → (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n, (∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 n (by simp) U x = Sec.res x z) ∧ ∀ (p : ℕ) s h U x, ev α.1 (p + 1) s h U x = 0) ∧ ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n, Sec.map (I.d n k) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 ∧ (CohomologyClass.mk α = 0 ↔ ∃ y : Sec (I.X m) X, Sec.map (I.d m n) y = ev α.1 0 n (by simp) X (𝟙 X))

def L_res_sec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ z : Sec ((res R F).X 0) U, Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z) ∧ Function.Injective (Sec.map (resι R F) (U := U)) ∧ (∀ (m n k : ℤ), 0 < n → m + 1 = n → ∀ z : Sec ((res R F).X n) U, n + 1 = k → Sec.map ((res R F).d n k) z = 0 → Loc U fun V g => ∃ y : Sec ((res R F).X m) V, Sec.map ((res R F).d m n) y = Sec.res g z) ∧ ∀ n : ℤ, n < 0 → Subsingleton (Sec ((res R F).X n) U)

section Basic
variable {R : Type} [CommRing R]

/- English proof (translation)
The claim follows from `(ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm`.
-/
theorem sec_res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm

/- English proof (translation)
Use `show (F.obj.map (k ≫ g).op).hom x = (F.obj.map k.op).hom ((F.obj.map g.op).hom x)`. Rewrite using `[op_comp, Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem sec_res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  show (F.obj.map (k ≫ g).op).hom x = (F.obj.map k.op).hom ((F.obj.map g.op).hom x)
  rw [op_comp, Functor.map_comp]
  rfl

/- English proof (translation)
The claim follows from `map_zero _`.
-/
theorem sec_res_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sec_map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

/- English proof (translation)
The claim follows from `LinearMap.map_add _ _ _`.
-/
theorem sec_map_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := LinearMap.map_add _ _ _

/- English proof (translation)
Simplify using `[Sec.map]`.
-/
theorem sec_map_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := by
  simp [Sec.map]

end Basic

/- English proof (translation)
Take `⟨p, hp⟩` from `Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ`. Establish `h` using `congrArg (Polynomial.aeval ζ.1) hp`. Simplify using `only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, ζ.2.2, zero_mul] at h`. Conclude with `sub_eq_zero.mp h`.
-/
theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, ζ.2.2, zero_mul] at h
  exact sub_eq_zero.mp h

/- English proof (translation)
The claim follows from `IsUnit.of_pow_eq_one (prim_pow ζ) (NeZero.ne q)`.
-/
theorem prim_isUnit {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : IsUnit ζ.1 :=
  IsUnit.of_pow_eq_one (prim_pow ζ) (NeZero.ne q)

/- English proof (translation)
Rewrite using `[← map_pow, h]`. Use `ext`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem units_root {q : ℕ} {X U V : Scheme.{0}} (u : (Γ(X, ⊤))ˣ) (x : U ⟶ X) (g : V ⟶ U) (w : (Γ(U, ⊤))ˣ)
    (h : w ^ q = Units.map x.appTop.hom.toMonoidHom u) :
    (Units.map g.appTop.hom.toMonoidHom w) ^ q = Units.map (g ≫ x).appTop.hom.toMonoidHom u := by
  rw [← map_pow, h]
  ext
  simp
  rfl

section Kum
variable (q : ℕ) [NeZero q]

/- English proof (translation)
The claim follows from `((hR (ZMod q) (tw q 1) U).1 _).2 ⟨twGen 1 ζ, rfl⟩`.
-/
theorem d_resGen (hR : L_res_sec) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (resGen 1 ζ) = 0 :=
  ((hR (ZMod q) (tw q 1) U).1 _).2 ⟨twGen 1 ζ, rfl⟩

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero`. Introduce `v w h`. Establish `: w = v` using `Units.ext (by simpa using h)`. Substitute `this` using the available equality.

Both sides reduce to the same expression. Consider the case `succ a ih`. Introduce `v w h`. Set `m : (Γ(U, ⊤))ˣ` to `(prim_isUnit ζ).unit ^ a * v`. Establish `hm : (m : Γ(U, ⊤)) = ζ.1 ^ a * v` using `by simp [m]`.

Establish `hw : (w : Γ(U, ⊤)) = ζ.1 * m` using `by rw [h, hm, pow_succ]; ring`. Rewrite using `[(hK q).2 U ζ m w hw, sec_map_add, d_resGen q hR, add_zero]`. Conclude with `ih v m hm`.
-/
theorem dt_pow (hK : L_kumT_ex) (hR : L_res_sec) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (a : ℕ) :
    ∀ v w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ a * v →
      Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U v) := by
  induction a with
  | zero =>
    intro v w h
    have : w = v := Units.ext (by simpa using h)
    subst this; rfl
  | succ a ih =>
    intro v w h
    let m : (Γ(U, ⊤))ˣ := (prim_isUnit ζ).unit ^ a * v
    have hm : (m : Γ(U, ⊤)) = ζ.1 ^ a * v := by simp [m]
    have hw : (w : Γ(U, ⊤)) = ζ.1 * m := by rw [h, hm, pow_succ]; ring
    rw [(hK q).2 U ζ m w hw, sec_map_add, d_resGen q hR, add_zero]
    exact ih v m hm

/- English proof (translation)
Set `ρ : (Γ(W, ⊤))ˣ` to `w2 * w1⁻¹`. Establish `hρ : ρ ^ q = 1`. Simplify using `only [ρ]`. Rewrite using `[mul_pow, inv_pow, ← h, mul_inv_cancel]`. Apply `(hG (ZMod q) _ W).1` to reduce the goal to its premises.

Take `⟨S, hS, hPS⟩` from `(hP q W).1 hqW`. Use `⟨S, hS, fun V g hg => ?_⟩` and prove the remaining obligations. Take `⟨ζ⟩` from `hPS V g hg`. Establish `hqV : IsUnit (q : Γ(V, ⊤))` using `by simpa using hqW.map g.appTop.hom`. Establish `hr : (g.appTop.hom (ρ : Γ(W, ⊤))) ^ q = 1`.

Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, hρ, Units.val_one, map_one]`. Rewrite using `[sec_res_map, sec_res_map, (hK q).1 V W g w1 hqW, (hK q).1 V W g w2 hqW]`. Apply `(hG (ZMod q) _ V).1` to reduce the goal to its premises. Take `⟨T, hT, hPT⟩` from `(hP q V).2.2.1 ζ _ hr`. Use `⟨T, hT, fun V' k hk => ?_⟩` and prove the remaining obligations.

Simplify using `only`. Take `⟨a, ha⟩` from `hPT V' k hk`. Rewrite using `[sec_res_map, sec_res_map, (hK q).1 V' V k _ hqV, (hK q).1 V' V k _ hqV]`. Use `symm`. Apply `dt_pow q hK hR (Prim.map k.appTop.hom ζ) a` to reduce the goal to its premises.

Establish `e : (w2 : Γ(W, ⊤)) = (ρ : Γ(W, ⊤)) * w1` using `by simp [ρ]`. Express the relevant statement in the definitionally equal form `k.appTop.hom (g.appTop.hom (w2 : Γ(W, ⊤))) = (k.appTop.hom ζ.1) ^ a * k.appTop.hom (g.appTop.hom (w1 : Γ(W, ⊤)))`. Rewrite using `[e, map_mul, map_mul, ha]`.
-/
theorem dt_root (hK : L_kumT_ex) (hP : L_prim_loc) (hG : L_sec_glue) (hR : L_res_sec) {W : Scheme.{0}}
    (hqW : IsUnit (q : Γ(W, ⊤))) (w1 w2 : (Γ(W, ⊤))ˣ) (h : w1 ^ q = w2 ^ q) :
    Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q W w1) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q W w2) := by
  let ρ : (Γ(W, ⊤))ˣ := w2 * w1⁻¹
  have hρ : ρ ^ q = 1 := by
    simp only [ρ]; rw [mul_pow, inv_pow, ← h, mul_inv_cancel]
  apply (hG (ZMod q) _ W).1
  obtain ⟨S, hS, hPS⟩ := (hP q W).1 hqW
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hPS V g hg
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hqW.map g.appTop.hom
  have hr : (g.appTop.hom (ρ : Γ(W, ⊤))) ^ q = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hρ, Units.val_one, map_one]
  rw [sec_res_map, sec_res_map, (hK q).1 V W g w1 hqW, (hK q).1 V W g w2 hqW]
  apply (hG (ZMod q) _ V).1
  obtain ⟨T, hT, hPT⟩ := (hP q V).2.2.1 ζ _ hr
  refine ⟨T, hT, fun V' k hk => ?_⟩
  dsimp only
  obtain ⟨a, ha⟩ := hPT V' k hk
  rw [sec_res_map, sec_res_map, (hK q).1 V' V k _ hqV, (hK q).1 V' V k _ hqV]
  symm
  apply dt_pow q hK hR (Prim.map k.appTop.hom ζ) a
  have e : (w2 : Γ(W, ⊤)) = (ρ : Γ(W, ⊤)) * w1 := by simp [ρ]
  change k.appTop.hom (g.appTop.hom (w2 : Γ(W, ⊤))) = (k.appTop.hom ζ.1) ^ a * k.appTop.hom (g.appTop.hom (w1 : Γ(W, ⊤)))
  rw [e, map_mul, map_mul, ha]

end Kum

/- English proof (translation)
Introduce `q _ X u hq`. Establish `hqU : ∀ {U : Scheme.{0}} (x : U ⟶ X), IsUnit (q : Γ(U, ⊤))` using `fun x => by simpa using hq.map x.appTop.hom`. Establish `key : ∀ {U : Scheme.{0}} (x : U ⟶ X) (w1 w2 : (Γ(U, ⊤))ˣ), w1 ^ q = Units.map x.appTop.hom.toMonoidHom u → w2 ^ q = Units.map x.appTop.hom.toMonoidHom u → Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w1) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w2)` using `fun x w1 w2 h1 h2 => dt_root q hK hP hG hR (hqU x) w1 w2 (h1.trans h2.symm)`. Take `⟨S, hS, hroot⟩` from `(hP q X).2.2.2 hq u`. Use `choose v hv using hroot`.

Take `⟨z, hz⟩` from `(hG (ZMod q) ((res (ZMod q) (tw q 1)).X 1) X).2 S hS (fun V g hg => Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q V (v V g hg))) (by`. Introduce `V W g k hg`. Rewrite using `[sec_res_map, (hK q).1 W V k _ (hqU g)]`. Conclude with `key (k ≫ g) _ _ (units_root u g k _ (hv V g hg)) (hv W (k ≫ g) _))`. Establish `hdz : Sec.map ((res (ZMod q) (tw q 1)).d 1 2) z = 0`.

Apply `(hG (ZMod q) _ X).1` to reduce the goal to its premises. Use `⟨S, hS, fun V g hg => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[sec_res_map, hz V g hg, sec_res_zero, ← sec_map_comp, HomologicalComplex.d_comp_d, sec_map_zero]`. Take `⟨α, hα0, hα1⟩` from `(hC (ZMod q) X (res (ZMod q) (tw q 1)) 0 1 2 (by norm_num) (by norm_num)).1 z hdz`.

Use `⟨α, fun U x => hα1 0 0 _ U x, fun U x w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[hα0 U x]`. Apply `(hG (ZMod q) _ U).1` to reduce the goal to its premises. Use `⟨S.pullback x, (Scheme.etaleTopology).pullback_stable x hS, fun V g hg => ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← sec_res_comp, hz V (g ≫ x) hg, sec_res_map, (hK q).1 V U g w (hqU x)]`. Conclude with `key (g ≫ x) _ _ (hv V (g ≫ x) hg) (units_root u x g w hw)`.
-/
theorem kum_exists_of (hK : L_kumT_ex) (hP : L_prim_loc) (hG : L_sec_glue) (hC : L_sch_cls) (hR : L_res_sec) :
    kum_exists := by
  intro q _ X u hq
  have hqU : ∀ {U : Scheme.{0}} (x : U ⟶ X), IsUnit (q : Γ(U, ⊤)) := fun x => by simpa using hq.map x.appTop.hom
  have key : ∀ {U : Scheme.{0}} (x : U ⟶ X) (w1 w2 : (Γ(U, ⊤))ˣ), w1 ^ q = Units.map x.appTop.hom.toMonoidHom u →
      w2 ^ q = Units.map x.appTop.hom.toMonoidHom u →
      Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w1) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w2) :=
    fun x w1 w2 h1 h2 => dt_root q hK hP hG hR (hqU x) w1 w2 (h1.trans h2.symm)
  obtain ⟨S, hS, hroot⟩ := (hP q X).2.2.2 hq u
  choose v hv using hroot
  obtain ⟨z, hz⟩ := (hG (ZMod q) ((res (ZMod q) (tw q 1)).X 1) X).2 S hS
    (fun V g hg => Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q V (v V g hg))) (by
      intro V W g k hg
      rw [sec_res_map, (hK q).1 W V k _ (hqU g)]
      exact key (k ≫ g) _ _ (units_root u g k _ (hv V g hg)) (hv W (k ≫ g) _))
  have hdz : Sec.map ((res (ZMod q) (tw q 1)).d 1 2) z = 0 := by
    apply (hG (ZMod q) _ X).1
    refine ⟨S, hS, fun V g hg => ?_⟩
    dsimp only
    rw [sec_res_map, hz V g hg, sec_res_zero, ← sec_map_comp, HomologicalComplex.d_comp_d, sec_map_zero]
  obtain ⟨α, hα0, hα1⟩ := (hC (ZMod q) X (res (ZMod q) (tw q 1)) 0 1 2 (by norm_num) (by norm_num)).1 z hdz
  refine ⟨α, fun U x => hα1 0 0 _ U x, fun U x w hw => ?_⟩
  rw [hα0 U x]
  apply (hG (ZMod q) _ U).1
  refine ⟨S.pullback x, (Scheme.etaleTopology).pullback_stable x hS, fun V g hg => ?_⟩
  dsimp only
  rw [← sec_res_comp, hz V (g ≫ x) hg, sec_res_map, (hK q).1 V U g w (hqU x)]
  exact key (g ≫ x) _ _ (hv V (g ≫ x) hg) (units_root u x g w hw)

end LateralTheory.EtaleFoundations
