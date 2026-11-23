module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEqSmulOfIsot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalEigenvaluesIndependentOfStandardFrame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0076
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Formalism.FormalDegreeBessel.StatementIO
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIso
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0289

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugacyClassesEquivUnitsModNormsNonspli
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TwClassForms

theorem twConj_gram (L : Type) [Field L] (c : L →+* L) (a : ℕ) (δ q : GL (Fin a) L) :
    (((q⁻¹ * δ * thetaGL a c q).val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ =
      q.valᵀ * ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ * q.val.map c := by
  have hΦ : GlobalTheory.Tw.Phi a L * (GlobalTheory.Tw.Phi a L)ᵀ = 1 := Phi_mul_transpose a L
  have hΦ' : (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L = 1 := mul_eq_one_comm.1 hΦ
  have hinv : (GlobalTheory.Tw.Phi a L)⁻¹ = (GlobalTheory.Tw.Phi a L)ᵀ := Matrix.inv_eq_left_inv hΦ'
  have hθ : (thetaGL a c q).val =
      GlobalTheory.Tw.Phi a L * ((GeneralLinearGroup.map c q)⁻¹).valᵀ * (GlobalTheory.Tw.Phi a L)ᵀ := rfl
  have hC : ((GeneralLinearGroup.map c q)⁻¹).valᵀ * (q.val.map c)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, show q.val.map c = (GeneralLinearGroup.map c q).val from rfl,
      Units.mul_inv, Matrix.transpose_one]
  have k1 : ∀ X : Matrix (Fin a) (Fin a) L, (GlobalTheory.Tw.Phi a L)ᵀ * (GlobalTheory.Tw.Phi a L * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hΦ', Matrix.one_mul]
  have k2 : ∀ X : Matrix (Fin a) (Fin a) L, ((GeneralLinearGroup.map c q)⁻¹).valᵀ * ((q.val.map c)ᵀ * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hC, Matrix.one_mul]
  have k3 : ∀ X : Matrix (Fin a) (Fin a) L, GlobalTheory.Tw.Phi a L * ((GlobalTheory.Tw.Phi a L)ᵀ * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hΦ, Matrix.one_mul]
  have k4 : ∀ X : Matrix (Fin a) (Fin a) L, δ.val * ((δ⁻¹).val * X) = X := by
    intro X; rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hY : (q⁻¹ * δ * thetaGL a c q).val * GlobalTheory.Tw.Phi a L *
      ((q.val.map c)ᵀ * (GlobalTheory.Tw.Phi a L)ᵀ * (δ⁻¹).val * q.val) = 1 := by
    simp only [Units.val_mul, hθ, Matrix.mul_assoc, k1, k2, k3, k4]
    exact Units.inv_mul q
  rw [Matrix.inv_eq_right_inv hY, Matrix.mul_inv_rev, hinv, ← Matrix.coe_units_inv]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem gram_delta (L : Type) [Field L] (a : ℕ) :
    (∀ G : Matrix (Fin a) (Fin a) L, IsUnit G.det → ∃ δ : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = G) ∧
    (∀ δ δ' : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = ((δ'.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ → δ = δ') := by
  have hΦ : GlobalTheory.Tw.Phi a L * (GlobalTheory.Tw.Phi a L)ᵀ = 1 := Phi_mul_transpose a L
  have hΦ' : (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L = 1 := mul_eq_one_comm.1 hΦ
  have hdΦ : IsUnit (GlobalTheory.Tw.Phi a L).det := Matrix.isUnit_det_of_right_inverse hΦ
  refine ⟨fun G hG => ?_, fun δ δ' h => ?_⟩
  · have hGT : IsUnit (Gᵀ)⁻¹.det := by
      rw [Matrix.det_nonsing_inv, Matrix.det_transpose]; exact hG.ringInverse
    have hd : IsUnit ((Gᵀ)⁻¹ * (GlobalTheory.Tw.Phi a L)ᵀ).det := by
      rw [Matrix.det_mul, Matrix.det_transpose]; exact hGT.mul hdΦ
    refine ⟨Matrix.nonsingInvUnit _ hd, ?_⟩
    change (((Gᵀ)⁻¹ * (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = G
    rw [Matrix.mul_assoc, hΦ', Matrix.mul_one, Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hG),
      Matrix.transpose_transpose]
  · have hu : ∀ x : GL (Fin a) L, IsUnit (x.val * GlobalTheory.Tw.Phi a L).det := by
      intro x; rw [Matrix.det_mul]; exact (Matrix.isUnits_det_units x).mul hdΦ
    have h1 := congrArg Matrix.transpose h
    simp only [Matrix.transpose_transpose] at h1
    have h2 := congrArg Inv.inv h1
    rw [Matrix.nonsing_inv_nonsing_inv _ (hu δ), Matrix.nonsing_inv_nonsing_inv _ (hu δ')] at h2
    have h3 := congrArg (· * (GlobalTheory.Tw.Phi a L)ᵀ) h2
    simp only [Matrix.mul_assoc, hΦ, Matrix.mul_one] at h3
    exact Units.ext h3

theorem herm_norm_basis (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (a : ℕ) (β t : B.Aˣ)
    (b : Module.Basis (Fin a) K.E B.A) : ∃ b' : Module.Basis (Fin a) K.E B.A,
      ∀ i j, B.herm ((β : B.A) * (t * B.σ t)) (b i) (b j) = B.herm β (b' i) (b' j) := by
  let f : B.A ≃ₗ[K.E] B.A := LinearEquiv.ofLinear (LinearMap.mulLeft K.E (t : B.A))
    (LinearMap.mulLeft K.E ((t⁻¹ : B.Aˣ) : B.A))
    (by ext y; simp [← mul_assoc]) (by ext y; simp [← mul_assoc])
  refine ⟨b.map f, fun i j => ?_⟩
  simp only [Module.Basis.map_apply, f, LinearEquiv.ofLinear_apply, LinearMap.mulLeft_apply,
    GlobalTheory.UnitLemma.InvAlg.herm, map_mul]
  congr 1
  ring

theorem twCl_equiv_cl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → ∀ (B : GlobalTheory.UnitLemma.InvAlg K), B.g * B.σ B.g = 1 → B.P = Q.map e.symm.toRingHom → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (a - 1) * B.g) → ∃ F : B.Cl ≃ {c : TwCl (thL a w) // (nrmL a w c.rep).val.charpoly = Q}, ∀ k : B.Cl, ∃ b : Module.Basis (Fin a) K.E B.A, ∀ i j, (((F k).1.rep.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm ((β₀ : B.A) * k.rep) (b i) (b j)) := by
  intro E _ _ _ hE w hw K e he hO a Q hQm hQd hQs B hg hP β₀ hβ₀
  have hthL : thL a w = thetaGL a (cj w) := by rw [thL, if_neg hw]
  have hnrm : ∀ y, nrmL a w y = y * thetaGL a (cj w) y := by intro y; rw [nrmL, if_neg hw]
  have hcc : ∀ x, cj w (cj w x) = x := by
    intro x; obtain ⟨y, rfl⟩ := e.surjective x; rw [← he, ← he, K.c_c]
  have hPsep : B.P.Separable := by rw [hP]; exact hQs.map
  have hfr : Module.finrank K.E B.A = a := by
    rw [← LinearMap.charpoly_natDegree (LinearMap.mulLeft K.E B.g)]
    change B.P.natDegree = a
    rw [hP, natDegree_map, hQd]
  let b0 : Module.Basis (Fin a) K.E B.A := Module.finBasisOfFinrankEq K.E B.A hfr
  have hε : ((-1 : B.A) ^ (a - 1) = 1 ∨ (-1 : B.A) ^ (a - 1) = -1) := neg_one_pow_eq_or B.A (a - 1)
  have hβx : ∀ x : B.Aˣ, B.σ (x : B.A) = x →
      B.σ ((β₀ * x : B.Aˣ) : B.A) = (β₀ * x : B.Aˣ) * ((-1) ^ (a - 1) * B.g) := by
    intro x hx; simp only [Units.val_mul, map_mul, hβ₀, hx]; ring

  have htwE : ∀ δ δ' : GLw a w, Relation.EqvGen (fun x y : GLw a w => ∃ g, y = g⁻¹ * x * thL a w g) δ δ' →
      ∃ q, δ' = q⁻¹ * δ * thL a w q := by
    intro δ δ' h
    induction h with
    | rel x y hxy => exact hxy
    | refl x => exact ⟨1, by simp⟩
    | symm x y _ ih =>
      obtain ⟨q, rfl⟩ := ih
      exact ⟨q⁻¹, by simp [mul_assoc]⟩
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨q, rfl⟩ := ih1
      obtain ⟨r, rfl⟩ := ih2
      exact ⟨q * r, by simp [mul_assoc]⟩
  have hσinv : ∀ u : B.Aˣ, B.σ ((u⁻¹ : B.Aˣ) : B.A) * B.σ (u : B.A) = 1 := by
    intro u; rw [← map_mul, Units.inv_mul, map_one]
  have hclE : ∀ x y : {x : B.Aˣ // B.σ (x : B.A) = x}, Relation.EqvGen (fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} =>
      ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))) x y → ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A)) := by
    intro x y h
    induction h with
    | rel x y hxy => exact hxy
    | refl x => exact ⟨1, by simp⟩
    | symm x y _ ih =>
      obtain ⟨u, hu⟩ := ih
      refine ⟨u⁻¹, ?_⟩
      have h1 := hσinv u
      have h2 : ((u⁻¹ : B.Aˣ) : B.A) * u = 1 := Units.inv_mul u
      rw [hu]
      linear_combination (-(x.1 : B.A) * (B.σ ((u⁻¹ : B.Aˣ) : B.A) * B.σ (u : B.A))) * h2 - (x.1 : B.A) * h1
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨u, hu⟩ := ih1
      obtain ⟨v, hv⟩ := ih2
      exact ⟨u * v, by rw [hv, hu, Units.val_mul, map_mul]; ring⟩

  obtain ⟨F0i, F0u⟩ := gram_delta (w.adicCompletion E) a
  have hF1 := _root_.GlobalTheory.GramTwistNorm.gram_twisted_norm_charpoly K B (w.adicCompletion E) e (cj w) he hcc a Q hP hQs hQd
  have hF4 := _root_.GlobalTheory.GramChange.gram_basis_change K B (w.adicCompletion E) e (cj w) he a
  have hF6 := twConj_gram (w.adicCompletion E) (cj w) a
  have hcl : ∀ k : B.Cl, B.σ (((Quot.out k).1 : B.Aˣ) : B.A) = (Quot.out k).1 := fun k => (Quot.out k).2
  have hG : ∀ k : B.Cl, IsUnit (Matrix.of fun i j => e (B.herm (((β₀ * (Quot.out k).1 : B.Aˣ)) : B.A) (b0 i) (b0 j))).det :=
    fun k => (hF1 _ (hβx _ (hcl k)) b0).1
  choose δk hδk using fun k => F0i _ (hG k)

  have hrep : ∀ k : B.Cl, ∀ δ : GLw a w, Relation.EqvGen (fun x y : GLw a w => ∃ g, y = g⁻¹ * x * thL a w g) (δk k) δ →
      ∃ b : Module.Basis (Fin a) K.E B.A, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ =
        Matrix.of fun i j => e (B.herm (((β₀ * (Quot.out k).1 : B.Aˣ)) : B.A) (b i) (b j)) := by
    intro k δ h
    obtain ⟨q, rfl⟩ := htwE _ _ h
    rw [hthL, hF6, hδk k]
    obtain ⟨b', hb'⟩ := (hF4 _ b0).1 q
    exact ⟨b', hb'.symm⟩
  let F : B.Cl → {c : TwCl (thL a w) // (nrmL a w c.rep).val.charpoly = Q} := fun k =>
    ⟨Quot.mk _ (δk k), by
      obtain ⟨b, hb⟩ := hrep k _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ (δk k)))).symm
      rw [hnrm]
      exact (hF1 _ (hβx _ (hcl k)) b).2 _ hb⟩
  have hinj : Function.Injective F := by
    intro k k' hkk
    have h1 : (Quot.mk _ (δk k) : TwCl (thL a w)) = Quot.mk _ (δk k') := congrArg Subtype.val hkk
    obtain ⟨b', hb'⟩ := hrep k _ (Quot.eqvGen_exact h1)
    rw [hδk k'] at hb'
    obtain ⟨t, ht⟩ := _root_.GlobalTheory.UnitLemma.IsometryUnit.isometry_unit K B hPsep _ hε a _ _ (hβx _ (hcl k')) (hβx _ (hcl k)) b0 b' (fun i j => by
      have := congrFun (congrFun hb' i) j
      simpa using e.injective this)
    have hrel : (Quot.mk _ (Quot.out k') : B.Cl) = Quot.mk _ (Quot.out k) := by
      apply Quot.sound
      refine ⟨t, ?_⟩
      have h2 : ((β₀⁻¹ : B.Aˣ) : B.A) * β₀ = 1 := Units.inv_mul β₀
      simp only [Units.val_mul] at ht
      linear_combination ((β₀⁻¹ : B.Aˣ) : B.A) * ht - (((Quot.out k).1 : B.A) - ((Quot.out k').1 : B.A) * ((t : B.A) * B.σ (t : B.A))) * h2
    exact (Quot.out_eq k).symm.trans (hrel.symm.trans (Quot.out_eq k'))

  have hsurj : Function.Surjective F := by
    rintro ⟨cl, hclQ⟩
    have hQδ : ((Quot.out cl) * thetaGL a (cj w) (Quot.out cl)).val.charpoly = Q := by
      rw [← hnrm]; exact hclQ
    obtain ⟨β, hβ, b, hb⟩ := _root_.GlobalTheory.TwTraceForm.exists_trace_form K B (w.adicCompletion E) e (cj w) he hcc hg a Q hP hQs hQd _ hQδ
    have hx : B.σ (((β₀⁻¹ * β : B.Aˣ)) : B.A) = ((β₀⁻¹ * β : B.Aˣ) : B.A) := by
      have h1 : B.σ ((β₀⁻¹ : B.Aˣ) : B.A) * ((β₀ : B.A) * ((-1) ^ (a - 1) * B.g)) = 1 := by
        rw [← hβ₀, ← map_mul, Units.inv_mul, map_one]
      have h2 : ((β₀⁻¹ : B.Aˣ) : B.A) * β₀ = 1 := Units.inv_mul β₀
      simp only [Units.val_mul, map_mul, hβ]
      linear_combination (((β₀⁻¹ : B.Aˣ) : B.A) * β) * h1 - (B.σ ((β₀⁻¹ : B.Aˣ) : B.A) * β * ((-1) ^ (a - 1) * B.g)) * h2
    let k : B.Cl := Quot.mk _ ⟨β₀⁻¹ * β, hx⟩
    refine ⟨k, ?_⟩
    obtain ⟨u, hu⟩ := hclE _ _ (Quot.eqvGen_exact (Quot.out_eq k)).symm
    have hβu : ((β₀ * (Quot.out k).1 : B.Aˣ) : B.A) = (β : B.A) * ((u : B.A) * B.σ (u : B.A)) := by
      rw [Units.val_mul, hu, Units.val_mul]
      have h2 : (β₀ : B.A) * ((β₀⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv β₀
      linear_combination ((β : B.A) * ((u : B.A) * B.σ (u : B.A))) * h2
    obtain ⟨b'', hb''⟩ := herm_norm_basis K B a β u b0
    obtain ⟨P, hPb⟩ := (hF4 (β : B.A) b).2 b''
    have hmat : ((δk k).val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹ᵀ =
        (((P⁻¹ * Quot.out cl * thetaGL a (cj w) P)).val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹ᵀ := by
      rw [hF6, hb, ← hPb, hδk k]
      ext i j
      simp only [Matrix.of_apply, hβu, hb'']
    have hδeq := F0u _ _ hmat
    apply Subtype.ext
    change (Quot.mk _ (δk k) : TwCl (thL a w)) = cl
    rw [hδeq]
    have hθP : thL a w P = thetaGL a (cj w) P := by rw [hthL]
    exact (Quot.sound (⟨P, by rw [hθP]⟩ : ∃ g, P⁻¹ * Quot.out cl * thetaGL a (cj w) P = g⁻¹ * Quot.out cl * thL a w g)).symm.trans (Quot.out_eq cl)
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun k => ?_⟩
  obtain ⟨b, hb⟩ := hrep k _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ (δk k) : TwCl (thL a w)))).symm
  refine ⟨b, fun i j => ?_⟩
  have := congrFun (congrFun hb i) j
  rw [Matrix.of_apply, Units.val_mul] at this
  exact this

end GlobalTheory.TwClassForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartLeEigensystemPartPrincipalLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.PartTypeW

theorem part_in_eigenpart : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π i0 c, principalLevelFrame.IsEigOf (PW i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF π c → ∀ i, ∀ U ∈ principalLevelFrame.isotL R.θ (PW i) (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (R.eWf i (sg0 D A)) π, ∃ x ∈ Wcc R SF i c, (R.HW i _).e x = U := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s _hOk hC SF hSF n hF PY PW _hPY hPW π i0 c hEig i U hU
  have hLev := hC.lev

  have hN : ∀ (cc : ℕ) (P : Pl D.host.E), (((1 ^ cc : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro cc P h
    rw [one_pow, Nat.cast_one] at h
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have LO := fun (j : Fin D.R.m) (Lv : LevelP R.Pg D.R.r ℂ) (P : Pl D.host.E) (hG : Good R A.μ0 P) =>
    GlobalTheory.LevOp.level_operators (Wc D j) (R.βW j) (R.ΛW j) _ (R.datWp j Lv) (hLev.βW j).choose_spec P
      (hN _ P) (fun PP h => hG PP (h.imp id (fun h' => absurd h' (Finset.notMem_empty _))))
  have hGood := fun P => (GlobalTheory.GoodPrimes.good_primes R F hLev).2.2.1 SF hSF P

  have hU' := hU
  simp only [principalLevelFrame.isotL, Mult.goodPart, Submodule.mem_inf, LinearMap.mem_ker] at hU'
  obtain ⟨⟨hUM, hUe⟩, hUiso⟩ := hU'

  have hle : ∀ k ∈ levS (Wc D i) (R.βW i) (R.datWp i R.triv),
      k ∈ levS (Wc D i) (R.βW i) (R.datWp i (R.levL F false (sg0 D A))) ∧
        levChi (Wc D i) (R.βW i) (R.datWp i (R.levL F false (sg0 D A))) k =
          levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k := by
    intro k hk
    obtain ⟨h1, h2⟩ := GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) (R.levL F false (sg0 D A)) k hk
    obtain ⟨_, h3⟩ := GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) R.triv k hk
    exact ⟨h1, h2.trans h3.symm⟩
  have hU0 : U ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) :=
    GlobalTheory.HeckeParts.mult_mono hle hUM

  have hrange := (hC.models.HW i (sg0 D A)).2.1
  obtain ⟨x, hx⟩ : U ∈ LinearMap.range (R.HW i (sg0 D A)).e := by
    rw [hrange]; exact hU0
  refine ⟨x, ?_, hx⟩
  rw [GlobalTheory.Hk3.Wcc, Submodule.mem_comap, hx]
  refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hU0, LinearMap.mem_ker.2 hUe⟩, Submodule.mem_inf.2 ⟨hU0, ?_⟩⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  intro P d B hB
  obtain ⟨_, _, _, _, hoff, -⟩ := id hB
  have hG : Good R A.μ0 P := (hGood P).1 hoff
  have hSph : SphOp (Wc D i) P d B := (((LO i R.triv P hG).2.1 SF d B).1 hB).2
  obtain ⟨B0, hB0⟩ : IsLab (Wc D i0) P d :=
    (GlobalTheory.LabEq.isLab_W_iff (s := s) R F hC i0 P d hG).2.2
      ((GlobalTheory.LabEq.isLab_W_iff (s := s) R F hC i P d hG).2.1 ⟨B, hSph⟩)
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.SphScalar.spherical_scalar hF (PW i0) (hPW i0) π P d B0 hB0
  obtain ⟨⟨x0, hx0S, hx0, hx0T⟩, hEigOp, -⟩ := hEig
  have hB0full := ((LO i0 (R.levL F false (sg0 D A)) P hG).2.1 SF d B0).2 ⟨hoff, hB0⟩
  have hfix0 : ∀ κ, (PW i0).ψ κ ∈ GlobalTheory.Hk3.hyp (Wc D i0) P → Formalism.L2.NG.rt D.host.E n κ x0 = x0 := by
    intro κ hκ
    obtain ⟨h1, h2⟩ := (LO i0 (R.levL F false (sg0 D A)) P hG).1 _ hκ
    rw [hx0T κ h1]
    simp only [h2, one_smul]
  have hac : a = c P d := by
    have e2 := hEigOp P d B0 hB0full x0 hx0S hx0T
    rw [ha x0 hx0S hfix0] at e2
    exact smul_left_injective ℂ hx0 e2
  obtain ⟨hiff, htr⟩ := _root_.GlobalTheory.FrameTransport.sph_eigen_frame_indep hF (PW i) (PW i0) (hPW i) (hPW i0) P d
  have hvec : ∀ y ∈ π.S, (∀ κ, (PW i).ψ κ ∈ GlobalTheory.Hk3.hyp (Wc D i) P → Formalism.L2.NG.rt D.host.E n κ y = y) →
      principalLevelFrame.Hecke₃ (PW i) B y = c P d • y := by
    intro y hy hfy
    rw [htr B B0 hSph hB0 y hfy, ha y hy (fun κ hκ => hfy κ ((hiff κ).2 hκ)), hac]
  have hUfix : ∀ k ∈ GlobalTheory.Hk3.hyp (Wc D i) P, postOn (R.MW i (sg0 D A)) (principalLevelFrame.rtA k) U = U := by
    intro k hk
    obtain ⟨h1, h2⟩ := (LO i (R.levL F false (sg0 D A)) P hG).1 k hk
    have hl := principalLevelFrame.mult_lev hUM
    apply MultilinearMap.ext
    intro v
    funext g
    rw [Mult.postOn_apply]
    show U v (g * k) = U v g
    rw [hl v k h1 g, h2, one_mul]
  exact GlobalTheory.IsotSph.hecke_eq_smul_of_isot hF (PW i) (hPW i) R.θ (R.MW i (sg0 D A)) π P d B (c P d) hSph hvec U hUiso hUfix

end GlobalTheory.PartTypeW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIrreducibleIsAdmissible
section
open Formalism.MainNotions.S

namespace GlobalTheory.IrrAdm

theorem isIrrAdm_of_irred : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsURepOn (UJset ε) π → IsIrredOn (UJset ε) π → GlobalTheory.RealInd.IsIrrAdm ε π := by
  intro n ε H _ _ _ _ π hU hI
  have hK : ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, ‖π k v‖ = ‖v‖ := fun k hk v =>
    hU.2.1 k (GlobalTheory.GKModule.mem_UJset_of_mem_Kset hk) v
  refine ⟨inferInstance, ⟨hU.1, hU.2.2, hK, ?_⟩, hI⟩
  intro Λ
  classical
  by_cases hne : ∃ S₀ : Submodule ℂ H, S₀ ≤ ⊤ ∧ IsKTypeOf ε π Λ S₀
  · obtain ⟨S₀, -, hS₀⟩ := hne
    haveI : FiniteDimensional ℂ S₀ := hS₀.1
    have hY := (_root_.GlobalTheory.AdmUnitary.admissible_and_kFin_smooth n ε H π hU hI).1 S₀ hS₀.1 hS₀.2.1
    let b := Module.finBasis ℂ S₀
    choose Y hYf hvY hYB using fun i => hY (b i) (b i).2
    haveI : ∀ i, FiniteDimensional ℂ (Y i) := hYf
    refine Submodule.finiteDimensional_of_le (sSup_le fun S hS => ?_) (S₂ := ⨆ i, Y i)
    obtain ⟨B, hB, rfl⟩ := (_root_.GlobalTheory.KTypeHighest.ktype_highest_weight n ε H π hU.1 hU.2.2 hK).2 Λ S₀ S hS₀ hS.2
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    have hx' : (⟨x, hx⟩ : S₀) ∈ Submodule.span ℂ (Set.range b) := b.span_eq ▸ Submodule.mem_top
    have h2 := Submodule.apply_mem_span_image_of_mem_span S₀.subtype hx'
    rw [← Set.range_comp] at h2
    refine (Submodule.span_le.2 ?_) h2
    rintro _ ⟨i, rfl⟩
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, Function.comp_apply, Submodule.subtype_apply,
      SetLike.mem_coe]
    exact Submodule.mem_iSup_of_mem i (hYB i B hB _ (hvY i))
  · have : {S : Submodule ℂ H | S ≤ ⊤ ∧ IsKTypeOf ε π Λ S} = ∅ :=
      Set.eq_empty_of_forall_notMem fun S hS => hne ⟨S, hS⟩
    rw [this, sSup_empty]
    infer_instance

end GlobalTheory.IrrAdm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolEqIdxRatio
section
noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount.OrbKProd

open GlobalTheory.BCT GlobalTheory.BCT.OrbProd

theorem finsum_prod_mul {α β : Type} (u : α → ℂ) (v : β → ℂ) :
    ∑ᶠ z : α × β, u z.1 * v z.2 = (∑ᶠ a, u a) * ∑ᶠ b, v b := by
  by_cases hu : (Function.support u).Finite
  · by_cases hv : (Function.support v).Finite
    · exact finsum_prod_mul_of_finite u v hu hv
    · rw [finsum_of_infinite_support hv, mul_zero]
      by_cases h0 : ∀ a, u a = 0
      · simp [h0]
      · push_neg at h0
        obtain ⟨a, ha⟩ := h0
        apply finsum_of_infinite_support
        intro hfin
        apply hv
        refine (hfin.image Prod.snd).subset ?_
        intro b hb
        exact ⟨(a, b), by simp only [Function.mem_support] at hb ⊢; exact mul_ne_zero ha hb, rfl⟩
  · rw [finsum_of_infinite_support hu, zero_mul]
    by_cases h0 : ∀ b, v b = 0
    · simp [h0]
    · push_neg at h0
      obtain ⟨b, hb⟩ := h0
      apply finsum_of_infinite_support
      intro hfin
      apply hu
      refine (hfin.image Prod.fst).subset ?_
      intro a ha
      exact ⟨(a, b), by simp only [Function.mem_support] at ha ⊢; exact mul_ne_zero ha hb, rfl⟩

section Vol

variable {G : Type} [Group G]

theorem vol_eq_idxRatio (C H : Subgroup G) : vol C H = GlobalTheory.FunObj.idxRatio H C := rfl

theorem vol_prod {G' : Type} [Group G'] (C H : Subgroup G) (C' H' : Subgroup G') :
    vol (C.prod C') (H.prod H') = vol C H * vol C' H' := by
  unfold vol
  rw [relIndex_prod_prod, relIndex_prod_prod]
  push_cast
  exact mul_div_mul_comm _ _ _ _

theorem map_conj_mul (K : Subgroup G) (t x : G) :
    K.map (MulAut.conj (t * x)).toMonoidHom =
      (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
  have h := map_conj_mul_three_subgroup_of_mem K K.one_mem t x
  rwa [mul_one] at h

theorem inf_map_conj (T A : Subgroup G) {t : G} (ht : t ∈ T) :
    T ⊓ A.map (MulAut.conj t).toMonoidHom = (T ⊓ A).map (MulAut.conj t).toMonoidHom := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective, map_conj_self _ ht]

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Vol

section Term

variable {G : Type} [Group G]

def oTerm (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) (x : G) : ℂ :=
  ((vol C (twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom) : ℚ) : ℂ)⁻¹ * f (x⁻¹ * δ * θ x)

theorem orbC_eq (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) :
    orbC θ K C δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G), oTerm θ K C δ f (Quotient.out q) :=
  rfl

theorem f_inv (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (hf : ∀ k ∈ K, ∀ y, f (k⁻¹ * y * θ k) = f y)
    {t k : G} (ht : t ∈ twCent θ δ) (hk : k ∈ K) (x : G) :
    f ((t * x * k)⁻¹ * δ * θ (t * x * k)) = f (x⁻¹ * δ * θ x) := by
  have ht0 : t * δ = δ * θ t := ht
  have ht' : θ t = δ⁻¹ * (t * δ) := eq_inv_mul_of_mul_eq ht0.symm
  rw [← hf k hk (x⁻¹ * δ * θ x)]
  congr 1
  simp only [map_mul, _root_.mul_inv_rev, ht']
  group

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Term

end GlobalTheory.LKCount.OrbKProd
end
end

