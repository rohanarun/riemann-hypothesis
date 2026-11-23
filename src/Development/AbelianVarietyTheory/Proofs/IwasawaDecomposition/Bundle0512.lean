module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertible
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigCoord

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.FlagBundle
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (IsUnivChart sp)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ (Over.pullback x).obj Z.t.G}

theorem exists_basis (hx : IsUnivChart _ n xc) (g : EigFrame Z φ x) (τ : E →+* ℂ) :
    ∃ B : Module.Basis (Fin (Dw.mult τ)) R (eig c φ hx τ), ∀ i, g.v τ i = vec Z.t x xc (B i) := by
  choose e he using fun i => vec_exists hx (g.v τ i) (g.tan τ i)
  have hm : ∀ i, e i ∈ eig c φ hx τ := fun i => (vec_eig_iff hx _ _).1 (by rw [← he i]; exact g.eig τ i)
  let b : Fin (Dw.mult τ) → eig c φ hx τ := fun i => ⟨e i, hm i⟩
  have key : ∀ w : eig c φ hx τ, ∃! a : Fin (Dw.mult τ) → R, ∑ j, a j • b j = w := fun w => by
    have h := g.basis τ (vec Z.t x xc w) (vec_tan hx _) ((vec_eig_iff hx _ _).2 w.2)
    rw [show g.v τ = fun j => vec Z.t x xc (e j) from funext he] at h
    simp only [comb_iff hx] at h
    refine (existsUnique_congr fun a => ?_).1 h
    rw [Subtype.ext_iff, eq_comm]
    simp [b]
  have li : LinearIndependent R b := Fintype.linearIndependent_iff.2 fun a ha i =>
    congrFun ((key 0).unique ha (show ∑ j, (0 : Fin (Dw.mult τ) → R) j • b j = 0 by simp)) i
  have sp' : ⊤ ≤ Submodule.span R (Set.range b) := fun w _ =>
    (Submodule.mem_span_range_iff_exists_fun R).2 (key w).exists
  exact ⟨Module.Basis.mk li sp', fun i => by rw [Module.Basis.mk_apply]; exact he i⟩

theorem exists_frame (hx : IsUnivChart _ n xc) (B : ∀ τ, Module.Basis (Fin (Dw.mult τ)) R (eig c φ hx τ)) :
    ∃ g : EigFrame Z φ x, ∀ τ i, g.v τ i = vec Z.t x xc (B τ i) := by
  refine ⟨⟨fun τ i => vec Z.t x xc (B τ i), fun τ i => vec_tan hx _, fun τ i => (vec_eig_iff hx _ _).2 (B τ i).2,
    fun τ w hw he => ?_⟩, fun _ _ => rfl⟩
  obtain ⟨cc, rfl⟩ := vec_exists hx w hw
  let v : eig c φ hx τ := ⟨cc, (vec_eig_iff hx _ _).1 he⟩
  have k : ∀ a, IsCombAtG Z.t x (fun i => vec Z.t x xc (B τ i)) a (vec Z.t x xc cc) ↔ (B τ).equivFun v = a := fun a => by
    rw [comb_iff hx, ← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp [v]
  simp only [k]
  exact existsUnique_eq'

theorem exists_basis_of_isUnit {M ι : Type} [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
    (B : Module.Basis ι R M) (A : Matrix ι ι R) (h : IsUnit A.det) :
    ∃ B' : Module.Basis ι R M, ∀ i, B' i = ∑ j, A i j • B j := by
  refine ⟨B.map (Matrix.toLinearEquiv B A.transpose (by rwa [Matrix.det_transpose])), fun i => ?_⟩
  simp [Matrix.toLin_self]

theorem isUnit_det_of_basis {M ι : Type} [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
    (B B' : Module.Basis ι R M) (A : Matrix ι ι R) (h : ∀ i, B' i = ∑ j, A i j • B j) : IsUnit A.det := by
  have e : A = (B.toMatrix B').transpose := by
    ext i j
    rw [Matrix.transpose_apply, Module.Basis.toMatrix_apply, h i, Module.Basis.repr_sum_self]
  rw [e, Matrix.det_transpose]
  exact B.isUnit_det B'

end GlobalTheory.ShFam.EigCoord


open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.EigCoord GlobalTheory.LieLocBasis in
theorem GlobalTheory.ShFam.EigCoord.coord_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (R' : Type) [CommRing R'] (φ' : c.F →+* R') (x' : Sp R' ⟶ Z.X) (ψ : R →+* R'), IsLocalRing R' → f.Stable → x' = spMap ψ ≫ x → φ' = ψ.comp φ → (∀ g : EigFrame Z φ' x', (∃! A : Mat Dw.mult R', f.Coord ψ g A) ∧ ∀ A, f.Coord ψ g A → ∀ τ, IsUnit (A τ).det) ∧ ∀ A : Mat Dw.mult R', (∀ τ, IsUnit (A τ).det) → ∃ g : EigFrame Z φ' x', f.Coord ψ g A := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f R' _ φ' x' ψ _ hf hx' hφ'
  subst hx' hφ'
  obtain ⟨g₀, hg₀⟩ := hf R' ψ
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t (spMap ψ ≫ x)
  choose B₀ hB₀ using exists_basis hx g₀
  have hv : ∀ τ, (fun k => spMap (dualMap ψ) ≫ f.v τ k) = g₀.v τ := fun τ => funext fun k => (hg₀ τ k).symm
  have key : ∀ (g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x))
      (B : ∀ τ, Module.Basis (Fin (Dw.mult τ)) R' (eig c (ψ.comp φ) hx τ)),
      (∀ τ i, g.v τ i = vec Z.t _ xc (B τ i)) → ∀ A : Mat Dw.mult R',
        f.Coord ψ g A ↔ ∀ τ i, B τ i = ∑ j, A τ i j • B₀ τ j := fun g B hB A => by
    simp only [EigFrame.Coord, true_and]
    refine forall_congr' fun τ => forall_congr' fun i => ?_
    rw [hv, hB, show g₀.v τ = fun j => vec Z.t _ xc (B₀ τ j) from funext (hB₀ τ), comb_iff hx, Subtype.ext_iff]
    simp
  refine ⟨fun g => ⟨?_, fun A hA τ => ?_⟩, fun A hA => ?_⟩
  · choose A hA hu using fun τ i => g₀.basis τ (g.v τ i) (g.tan τ i) (g.eig τ i)
    refine ⟨A, ⟨rfl, rfl, fun τ i => by rw [hv]; exact hA τ i⟩, fun A' hA' => ?_⟩
    funext τ i
    exact hu τ i _ (by have := hA'.2.2 τ i; rwa [hv] at this)
  · choose B hB using exists_basis hx g
    exact isUnit_det_of_basis (B₀ τ) (B τ) (A τ) ((key g B hB A).1 hA τ)
  · choose B hB using fun τ => exists_basis_of_isUnit (B₀ τ) (A τ) (hA τ)
    obtain ⟨g, hg⟩ := exists_frame hx B
    exact ⟨g, (key g B hg A).2 hB⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRing
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigStable

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap eigLat IsUnivChart scaleD sp)

attribute [local instance] Over.cartesianMonoidalCategory

theorem basis_fixed_bc {L k : Type} [CommRing L] [CommRing k] (ψ : L →+* k) {n m : ℕ}
    (P : Module.End L (Fin n → L)) (P' : Module.End k (Fin n → k)) (hP : ∀ c, P (P c) = P c)
    (h : ∀ c, P' (ψ ∘ c) = ψ ∘ P c) (e : Fin m → Fin n → L) (he : ∀ i, P (e i) = e i)
    (hb : ∀ c, P c = c → ∃! a : Fin m → L, c = ∑ i, a i • e i) (c' : Fin n → k) (hc : P' c' = c') :
    ∃! a : Fin m → k, c' = ∑ i, a i • (ψ ∘ e i) := by
  classical
  choose M hM using fun j : Fin n => (hb _ (hP (Pi.single j 1))).exists
  have hs : ∀ {R : Type} [CommRing R] (a : Fin n → R), ∑ j, a j • (Pi.single j 1 : Fin n → R) = a := fun a => by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hinv : ∀ i, (fun i' => ∑ j, e i j * M j i') = Pi.single i 1 := fun i => by
    refine (hb _ (he i)).unique ?_ ?_
    · set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← he i, ← hs (e i), map_sum]
      simp only [map_smul, hM, Finset.smul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    · simp [Pi.single_apply]
  have h1 : ∀ j, P' (Pi.single j 1) = ∑ i, ψ (M j i) • (ψ ∘ e i) := fun j => by
    rw [show (Pi.single j 1 : Fin n → k) = ψ ∘ Pi.single j 1 from funext fun j' => by
      by_cases hj : j' = j <;> simp [hj, Pi.single_apply], h, hM]
    funext r
    simp [Finset.sum_apply]
  refine ⟨fun i => ∑ j, c' j * ψ (M j i), ?_, fun a ha => ?_⟩
  · show c' = _
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← hc, ← hs c', map_sum]
    simp only [map_smul, h1, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  · funext i
    have h2 : ∀ i', ∑ j, ψ (e i' j) * ψ (M j i) = if i = i' then 1 else 0 := fun i' => by
      have := congrArg ψ (congrFun (hinv i') i)
      simpa [Pi.single_apply, apply_ite ψ] using this
    have h3 : ∀ j, c' j = ∑ i', a i' * ψ (e i' j) := fun j => by
      have := congrFun ha j
      simpa [Finset.sum_apply] using this
    show a i = ∑ j, c' j * ψ (M j i)
    simp only [h3, Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, h2]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {l : Level H} (c : Coeff l)

theorem exists_proj_bc {L : Type} [CommRing L] [IsLocalRing L] (φ : c.F →+* L) {x : Sp L ⟶ X} {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj t.G} (hx : IsUnivChart _ n xc)
    {k : Type} [CommRing k] (ψ : L →+* k) :
    ∃ (xc' : ∀ m : ℕ, sp (R₀ := k) (ReciprocityTheory.ChartRestriction.G.Chart.JetR k (Fin n) m) ⟶ (Over.pullback (spMap ψ ≫ x)).obj t.G)
      (hx' : IsUnivChart _ n xc'),
      (∀ cc : Fin n → L, vec t (spMap ψ ≫ x) xc' (ψ ∘ cc) =
        spMap (Formalism.L2.Pj.dualMap ψ) ≫ vec t x xc cc) ∧
      ∀ τ, ∃ (P : Module.End L (Fin n → L)) (P' : Module.End k (Fin n → k)), (∀ cc, P (P cc) = P cc) ∧
        (∀ cc, P' (ψ ∘ cc) = ψ ∘ P cc) ∧ (∀ cc, P cc = cc ↔ cc ∈ eig c φ hx τ) ∧
        ∀ cc, P' cc = cc ↔ cc ∈ eig c (ψ.comp φ) hx' τ := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  have key : ∀ (τ : E →+* ℂ) {R : Type} [CommRing R] [Algebra c.F R] {x : Sp R ⟶ X}
      {xc : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ (Over.pullback x).obj t.G}
      (hx : IsUnivChart _ n xc), (∀ m, proj (rho hx) (embK c) α τ (proj (rho hx) (embK c) α τ m) =
          proj (rho hx) (embK c) α τ m) ∧
        ∀ m, proj (rho hx) (embK c) α τ m = m ↔ m ∈ eig c (algebraMap c.F R) hx τ :=
    fun τ {R} _ _ {x xc} hx => by
      have e₁ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx) (embK c τ) (proj (rho hx) (embK c) α τ m) := fun m =>
        eig_of_alpha _ _ α hN τ (proj_eig_alpha _ _ α hinj f hf hfs τ m)
      have e₂ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx) (embK c τ) m → proj (rho hx) (embK c) α τ m = m := fun m hm => by
        have := proj_sum_eig (rho hx) (embK c) α hinj (Pi.single τ m) (fun τ' => by
          by_cases h : τ' = τ
          · subst h; rwa [Pi.single_eq_same]
          · rw [Pi.single_eq_of_ne h]; intro a; simp) τ
        rwa [Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_same] at this
      refine ⟨fun m => e₂ _ (e₁ m), fun m => ?_⟩
      rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
      exact ⟨fun h => h ▸ e₁ m, fun h => e₂ m h⟩
  letI : Algebra c.F L := φ.toAlgebra
  letI : Algebra L k := ψ.toAlgebra
  letI : Algebra c.F k := (ψ.comp φ).toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := k) hx
  have htm : ∀ (a : 𝓞 E) (cc : Fin n → L), rho hx' a (algebraMap L k ∘ cc) = algebraMap L k ∘ rho hx a cc :=
    fun a cc => vec_inj hx' (by
      show vec t _ xc' (tmap hx' _ _) = vec t _ xc' (_ ∘ tmap hx _ _)
      rw [vec_tmap hx', hv, hv, vec_tmap hx, Category.assoc])
  have pw : ∀ (j : ℕ) cc, (rho hx' α ^ j) (algebraMap L k ∘ cc) = algebraMap L k ∘ (rho hx α ^ j) cc := fun j => by
    induction j with
    | zero => exact fun _ => rfl
    | succ j ih => intro cc; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]; exact htm α _
  have pr : ∀ (Q : Polynomial c.F) cc, Polynomial.aeval (rho hx' α) (Q.map (algebraMap c.F k)) (algebraMap L k ∘ cc) =
      algebraMap L k ∘ Polynomial.aeval (rho hx α) (Q.map (algebraMap c.F L)) cc := fun Q cc => by
    induction Q using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq]
      funext j; simp
    | monomial j a =>
      rw [Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Module.End.mul_apply, Module.End.mul_apply, pw, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
      funext i
      exact (map_mul (algebraMap L k) _ _).symm
  exact ⟨xc', hx', hv, fun τ => ⟨_, _, (key τ hx).1, pr _, (key τ hx).2, (key τ hx').2⟩⟩

end GlobalTheory.ShFam.EigStable


open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.EigLoc GlobalTheory.LieLocBasis in
theorem GlobalTheory.ShFam.EigStable.stable_of_isLocalRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x), IsLocalRing R → GlobalTheory.ShFam.EigFrame.Stable f := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f _ R' _ _ ψ
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  obtain ⟨xc', hx', hv, hP⟩ := GlobalTheory.ShFam.EigStable.exists_proj_bc c φ hx ψ
  choose e he using fun τ i => vec_exists hx (f.v τ i) (f.tan τ i)
  choose P P' hPP hc hP hP' using hP
  have heig : ∀ τ i, P τ (e τ i) = e τ i := fun τ i =>
    (hP τ _).2 ((vec_eig_iff hx _ _).1 (by rw [← he]; exact f.eig τ i))
  have hfv : ∀ τ, f.v τ = fun i => vec Z.t x xc (e τ i) := fun τ => funext (he τ)
  refine ⟨⟨fun τ i => vec Z.t (spMap ψ ≫ x) xc' (ψ ∘ e τ i), fun τ i => vec_tan hx' _,
    fun τ i => (vec_eig_iff hx' _ _).2 ((hP' τ _).1 (by rw [hc, heig])), fun τ w hw hw' => ?_⟩,
    fun τ i => by rw [he]; exact hv _⟩
  obtain ⟨cc, rfl⟩ := vec_exists hx' w hw
  simp only [comb_iff hx']
  refine GlobalTheory.ShFam.EigStable.basis_fixed_bc ψ (P τ) (P' τ) (hPP τ) (hc τ) (e τ) (heig τ) (fun c₀ h₀ => ?_) cc
    ((hP' τ _).2 ((vec_eig_iff hx' _ _).1 hw'))
  have := f.basis τ _ (vec_tan hx c₀) ((vec_eig_iff hx _ _).2 ((hP τ _).1 h₀))
  rw [hfv] at this
  simpa only [comb_iff hx] using this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapLabelPartPreimageRationalSpan
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.PartSpan

theorem mem_span_rat {K V E : Type} [Field K] [AddCommGroup V] [Module ℂ V] [AddCommGroup E] [Module ℂ E]
    {τ : K →+* ℂ} {n : ℕ} (u : (Fin n → K) →ₛₗ[τ] V) (Φ : V →ₗ[ℂ] E) (P : Submodule ℂ E)
    (hinj : ∀ c : Fin n → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) = 0 → c = 0)
    (hspan : ∀ c : Fin n → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) ∈ P →
      Φ (∑ k, c k • u (Pi.single k 1)) ∈ Submodule.span ℂ (Φ '' {y | ∃ a, Φ (u a) ∈ P ∧ u a = y}))
    (x : V) (hx : x ∈ Submodule.span ℂ (Set.range u)) (hP : Φ x ∈ P) :
    x ∈ Submodule.span ℂ {y | ∃ a, Φ (u a) ∈ P ∧ u a = y} := by
  have hexp : ∀ a : Fin n → K, u a = ∑ k, τ (a k) • u (Pi.single k 1) := by
    intro a
    have ha : a = ∑ k, a k • (Pi.single k 1 : Fin n → K) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [ha]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ]
  have hsp : ∀ z ∈ Submodule.span ℂ (Set.range u), ∃ c : Fin n → ℂ, z = ∑ k, c k • u (Pi.single k 1) := by
    intro z hz
    have hle : Submodule.span ℂ (Set.range u) ≤ Submodule.span ℂ (Set.range fun k => u (Pi.single k 1)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, hexp]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hle hz)
    exact ⟨c, hc.symm⟩
  obtain ⟨c, rfl⟩ := hsp x hx
  have h1 := hspan c hP
  rw [← Submodule.map_span] at h1
  obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.1 h1
  have hsS : Submodule.span ℂ {y | ∃ a, Φ (u a) ∈ P ∧ u a = y} ≤ Submodule.span ℂ (Set.range u) :=
    Submodule.span_mono (by rintro _ ⟨a, -, rfl⟩; exact ⟨a, rfl⟩)
  obtain ⟨d, rfl⟩ := hsp w (hsS hw)
  have hcd : c - d = 0 := by
    apply hinj
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, map_sub, hwe, sub_self]
  rw [sub_eq_zero.1 hcd]
  exact hw


set_option maxHeartbeats 4000000 in
theorem mem_span_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix), ∀ x ∈ Submodule.span ℂ (Set.range fun a => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x) ∈ R.Wp3 i p → x ∈ Submodule.span ℂ {y | ∃ a, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p ∧ D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)) = y} := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t p x hx hW
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok.ok2
  have e1 := GlobalTheory.T.thetaMap_hilbertModel_eq_concreteThetaMap_familyThree D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t
  have h5 := hR.lifts0.1
  let Φ : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A3.A)).H :=
    (Y.mj.eW i).comp (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1))
  let u := ((D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)).comp (Y.eMt i t).toLinearMap).comp
    (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVecLin
  let m : (R.HW i (sg0 D A3.A)).H →ₛₗ[cj (twAt D.what₂.embLL A3.A.v0)] (R.toCx3 F).W i := Tw.mkL (twAt D.what₂.embLL A3.A.v0) _
  have hcon : ∀ a, m (Φ (u a)) =
      (R.toCx3 F).tC F.cr false i t (cpt A3.fam3.base3.v0.embedding a) := by
    intro a
    refine Eq.trans ?_ ((R.toCx3 F).tC_cpt_eq F.cr false i t a).symm
    show Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)
        (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))))) =
      R.phs i • Tw.map _ (R.thG i t) (Tw.semi _ R.toRealDat.emb0 (R.jV i t) (F.cr.toL (R.toCx3 F).zs false i t a))
    have h3' : F.cr.toL (R.toCx3 F).zs false i t a =
        LiftForms.lvlForm (A3.A.fam.L i t).S (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P (A3.A.fam.lvlA F.P0 F.ψ0).ψ
          (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a) :=
      (LiftForms.lvlForm_lE (v0 := A3.A.v0) ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩ a).symm
    rw [hP.phs i, one_smul, e1, h3']
    rfl

  have hsing : ∀ k : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)),
      cpt A3.fam3.base3.v0.embedding (Pi.single k (1 : D.what₂.LL)) = Pi.single k 1 := by
    intro k
    funext j
    by_cases h : j = k
    · subst h; simp [cpt]
    · simp [cpt, Pi.single_apply, h]
  have hsum : ∀ c : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) → ℂ, m (Φ (∑ k, c k • u (Pi.single k 1))) =
      (R.toCx3 F).tC F.cr false i t (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k)) := by
    intro c
    have hc : (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k)) =
        ∑ k, cj (twAt D.what₂.embLL A3.A.v0) (c k) • (Pi.single k 1 : Fin _ → ℂ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    refine Eq.trans ?_ (congrArg ((R.toCx3 F).tC F.cr false i t) hc).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Eq.trans ?_ (map_sum ((R.toCx3 F).tC F.cr false i t) (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k) • (Pi.single k 1 : Fin _ → ℂ)) Finset.univ).symm
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smulₛₗ]
    refine Eq.trans ?_ (map_smul ((R.toCx3 F).tC F.cr false i t) _ _).symm
    exact congrArg (fun z => cj (twAt D.what₂.embLL A3.A.v0) (c k) • z)
      ((hcon (Pi.single k 1)).trans (congrArg ((R.toCx3 F).tC F.cr false i t) (hsing k)))

  have hinj : ∀ c : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) = 0 → c = 0 := by
    intro c hc
    have h0 : (R.toCx3 F).tC F.cr false i t (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k)) =
        0 := by
      rw [← hsum c]
      show Tw.mk _ (Φ _) = 0
      rw [hc]
      rfl
    have h1 := (h5 i t).1 (h0.trans (map_zero _).symm)
    funext k
    have hk := congrArg (cj (twAt D.what₂.embLL A3.A.v0)) (congrFun h1 k)
    rw [Links.cj_cj] at hk
    exact hk.trans (map_zero (cj (twAt D.what₂.embLL A3.A.v0)))
  have hw0 := (R.toCx3 F).principal_form_injective false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) i
  have hC : (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≤
      Submodule.span ℂ (m '' (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y})) := by
    have hSpW : Submodule.span ℂ (m '' (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y})) ≤
        (R.toCx3 F).Wp i p := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩
      exact ha
    have hle := finrank_le_cpt A3.fam3.base3.v0.embedding ((R.toCx3 F).w0C false i) hw0
      (Submodule.span ℂ (m '' (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y})))
      ((R.toCx3 F).WpK false i p) (fun y hy => by
        obtain ⟨a, rfl⟩ := ((R.toCx3 F).liftMat_bij F.cr false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) h5 hR.ratTh i t).2 y
        have hk := (R.toCx3 F).key_lift F.cr false h5 hR.ratTh i t a
        have hy' : (R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding ((R.toCx3 F).liftMat F.cr false i t *ᵥ a)) ∈
            (R.toCx3 F).Wp i p := hy
        rw [hk, ← hcon a] at hy'
        rw [hk, ← hcon a]
        exact Submodule.subset_span ⟨Φ (u a), ⟨u a, ⟨a, hy', rfl⟩, rfl⟩, rfl⟩)
    rw [(R.toCx3 F).finrank_WpK F.cr false hR.h4pos hR.kForm hR.ewNorm hR.types0 h5 hR.ratTh hR.liftHyp0.h3W hR.partsW i p] at hle
    have heq := Submodule.eq_of_le_of_finrank_le (inf_le_inf_right _ hSpW) hle
    exact heq.symm.le.trans inf_le_left
  have hspan : ∀ c : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) ∈ R.Wp3 i p →
      Φ (∑ k, c k • u (Pi.single k 1)) ∈ Submodule.span ℂ (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y}) := by
    intro c hc
    have hm : m (Φ (∑ k, c k • u (Pi.single k 1))) ∈
        (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) := by
      refine ⟨hc, ?_⟩
      rw [← (h5 i t).2]
      exact ⟨_, (hsum c).symm⟩
    have h1 := hC hm
    rw [← Submodule.map_span] at h1
    obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.1 h1
    have hwe' : w = Φ (∑ k, c k • u (Pi.single k 1)) := hwe
    rw [← hwe']
    exact hw
  exact mem_span_rat u Φ (R.Wp3 i p) hinj hspan x hx hW

end GlobalTheory.Mem.R3.PartSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapSurjectiveOntoCuspFormsUsedTuple
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.LiftOnto


set_option maxHeartbeats 1000000 in
theorem thetaMap_surjective : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T), Used0 D (Y.tup t) → Function.Surjective (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i t _
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hb : Function.Bijective ((A3.indefDown (s0Of R F)).θ i t).mulVec :=
    CxData.liftMat_bij (R.toCx3 F) F.cr false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.lifts0.1 hR.ratTh i t
  have hB : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1 :=
    ⟨hH.ok.ok2.conj, hH.ok.ok2.irr, hH.ok.ok2.lifts i t⟩
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj hB
  obtain ⟨hTh, hθ⟩ := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hTh.span i, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨z, hz⟩ := hb.2 (Pi.single k 1)
  refine ⟨D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z)), ?_⟩
  have hz' : lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ
      (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) = z := by
    refine (Matrix.mulVec_mulVec _ _ _).trans ?_
    exact (congrArg (fun M => M *ᵥ z) hp.1).trans (Matrix.one_mulVec z)
  show _ = Z.jW i (Pi.single k 1)
  rw [hθ i t]
  exact congrArg (Z.jW i) ((congrArg (((A3.indefDown (s0Of R F)).θ i t).mulVec) hz').trans hz)

end GlobalTheory.Mem.LiftOnto

end
end

