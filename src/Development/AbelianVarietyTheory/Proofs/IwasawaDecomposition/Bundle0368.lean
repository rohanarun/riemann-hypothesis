module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Formalism.LocalToGlobal.Columns.Bundle0013
public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Formalism.LocalToGlobal.Columns.Bundle0019
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0354

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GloRhoZeroOfCompat
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.LevStd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem gloRho_eq_of_compat (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (w : Pl E) (e : (𝓞 E ⧸ w.asIdeal) ≃+* kv F v)
    (he : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : gloPhi v spl (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w z)) (z : Formalism.L2.Herm.intAf F E) :
    gloRho v spl halg z = e (resS F w z) := by
  obtain ⟨hz, h⟩ := he z
  rw [gloRho_apply]
  exact h

theorem gloRho_zero_of_compat (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (w : Pl E) (e : (𝓞 E ⧸ w.asIdeal) ≃+* kv F v)
    (he : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : gloPhi v spl (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w z)) :
    ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0 := by
  intro a ha
  rw [gloRho_eq_of_compat v spl halg w e he, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

theorem gloE_eq_of_compat (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (w : Pl E) (e : (𝓞 E ⧸ w.asIdeal) ≃+* kv F v)
    (he : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : gloPhi v spl (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w z)) (t : kP w) :
    gloE v spl halg w (gloRho_zero_of_compat v spl halg w e he) t = e t := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [← resS_oToS (F := F), gloE_resS, gloRho_eq_of_compat v spl halg w e he]

end GlobalTheory.Mem.LevStd


open GlobalTheory.Mem.LevStd in
theorem GlobalTheory.Mem.LevStd.levU_prod_glevH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (gp : Fin 2 → ℕ) (Jm : Matrix (Fin n) (Fin n) E) (S : StepLevel F E hc.sig Jm T f bad) (G : GLoc F E hc.sig gp) (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) (lamw : ∀ w, Hw w →* ℂˣ) (H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))) (lam : ∀ a v h, H a v h →* ℂˣ) (wOf : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → SG) (e : ∀ a v h, (𝓞 E ⧸ (wOf a v h).1.asIdeal) ≃+* kv F v), Jm = 1 → S.Lb = baseLb E n ST → ∀ hU : S.U = levU hc n ST SG (Subgroup.pi Set.univ Hw), (∀ x : S.U, S.chi x = ∏ w : SG, (lamw w ⟨(levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).1 w, (levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).2 w trivial⟩)⁻¹) → (∀ a v (_ : (gp a : 𝓞 F) ∈ v.asIdeal), v ∉ plUnder F ST) → (∀ a v h (w : SG), IsOver v w.1 ↔ w = wOf a v h) → (∀ φ : SG → ℂ, ∏ w : SG, φ w = ∏ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal), φ (wOf a v h)) → (∀ a v h (z : Formalism.L2.Herm.intAf F E), ∃ hz : G.phi a v h (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F, IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e a v h (resS F (wOf a v h).1 z)) → (∀ a v h M, M ∈ Hw (wOf a v h) ↔ Matrix.GeneralLinearGroup.map (e a v h).toRingHom M ∈ H a v h) → (∀ a v h (M : Hw (wOf a v h)) (M' : H a v h), M'.1 = Matrix.GeneralLinearGroup.map (e a v h).toRingHom M.1 → lam a v h M' = lamw (wOf a v h) M) → ∃ V : GLevH S G H lam, ∀ a v h, V.fr a v h = 1 := by
  intro F E _ _ _ _ _ _ hc n _ ST SG T f bad gp Jm S G Hw lamw H lam wOf e hJ hLb hU hchi hST hover hprod hcomp hH hlam
  subst hJ
  have hcomp' : ∀ a v h (z : Formalism.L2.Herm.intAf F E), ∃ hz : gloPhi v (G.sp a v h) (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e a v h (resS F (wOf a v h).1 z) := hcomp
  have hw := fun a v h => gloRho_zero_of_compat v (G.sp a v h) (G.sp_alg a v h) (wOf a v h).1 (e a v h) (hcomp' a v h)
  have hgE := fun a v h => gloE_eq_of_compat v (G.sp a v h) (G.sp_alg a v h) (wOf a v h).1 (e a v h) (hcomp' a v h)
  have hloc : ∀ v x, x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) →
      (x ∈ S.Uloc v ↔ x ∈ levLoc hc n ST SG (Subgroup.pi Set.univ Hw) v) := by
    intro v x hx
    constructor
    · intro hxv
      have hxU : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := hx.1
      have hp : rll_put n v x ∈ S.U := by
        refine (S.U_eq _).2 ⟨rll_put_mem_UAd hc n v hxU, fun v' => ?_⟩
        by_cases hv : v' = v
        · subst hv; rw [rll_put_self]; exact hxv
        · rw [rll_put_ne n v v' hv]; exact Subgroup.one_mem _
      rw [hU] at hp
      exact ⟨_, hp, rll_put_self n v x⟩
    · rintro ⟨k, hk, rfl⟩
      rw [← hU] at hk
      exact ((S.U_eq k).1 hk).2 v
  have hxL : ∀ x : S.U, x.1 ∈ levU hc n ST SG (Subgroup.pi Set.univ Hw) := fun x => hU ▸ x.2
  have hkJ : ∀ x : S.U, x.1 ∈ J0 hc n ST := fun x => ((mem_levU hc n ST SG _).1 (hxL x)).1
  refine ⟨{ fr := fun _ _ _ => 1
            fr_lat := ?_
            mem := ?_
            red := fun a v h x => ⟨Matrix.GeneralLinearGroup.map (e a v h).toRingHom
                ((levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).1 (wOf a v h)),
              (hH a v h _).1 ((levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).2 (wOf a v h) trivial)⟩
            red_eq := ?_
            chi_eq := ?_
            chi_unit := ?_ }, fun _ _ _ => rfl⟩
  · intro a v h x
    rw [hLb]
    exact gco_fr_lat n ST v (G.sp a v h) (G.sp_alg a v h) (hST a v h) x
  · intro a v h x hx
    rw [hLb] at hx
    have hG : ∀ y : GL (Fin n) (E ⊗[F] v.adicCompletion F), G.mat a v h 1 y =
        ((bc (gloPhi v (G.sp a v h)) y : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
      intro y; simp only [GLoc.mat, inv_one, one_mul, mul_one]; rfl
    rw [hloc v x hx, gco_mem_levLoc hc n ST SG v (G.sp a v h) (G.sp_alg a v h) Hw (wOf a v h) (hw a v h)
      ((hover a v h _).2 rfl) (fun w' hw' => (hover a v h w').1 hw') (hST a v h) x hx, hG]
    constructor
    · rintro ⟨M, hM, hMx⟩
      refine ⟨Matrix.GeneralLinearGroup.map (e a v h).toRingHom M, (hH a v h M).1 hM, ?_⟩
      rw [← hMx]
      ext i j
      rw [Matrix.map_apply, hgE]
      rfl
    · rintro ⟨M', hM', hM'x⟩
      refine ⟨Matrix.GeneralLinearGroup.map (e a v h).symm.toRingHom M', (hH a v h _).2 ?_, ?_⟩
      · convert hM' using 1
        ext i j
        simp
      · rw [← hM'x]
        ext i j
        rw [Matrix.map_apply, hgE]
        simp
  · intro a v h x
    have h1 := gco_red_map n v (G.sp a v h) (G.sp_alg a v h) (wOf a v h).1 (hw a v h) (congruence_subgroup_le_stabilizer hc n ST (hkJ x))
    have hG : G.mat a v h 1 (bc (prV (E := E) v) x.1) =
        ((bc (gloPhi v (G.sp a v h)) (bc (prV (E := E) v) x.1) : GL (Fin n) (v.adicCompletion F)) :
          Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
      simp only [GLoc.mat, inv_one, one_mul, mul_one]; rfl
    rw [hG, ← h1]
    ext i j
    rw [Matrix.map_apply, hgE]
    rfl
  · intro x
    rw [hchi x, Units.coe_prod]
    simp only [Units.val_inv_eq_inv_val]
    rw [hprod]
    congr 1; funext a; congr 1; funext v; congr 1; funext h
    rw [hlam a v h ⟨(levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hxL x⟩).1 (wOf a v h),
      (levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hxL x⟩).2 (wOf a v h) trivial⟩ _ rfl]
  · intro x
    rw [hchi x, Units.coe_prod, norm_prod]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [Units.val_inv_eq_inv_val, norm_inv, inv_eq_one]
    generalize (⟨_, _⟩ : Hw w) = m
    have hfo : IsOfFinOrder m := isOfFinOrder_of_finite m
    obtain ⟨N, hN, hpow⟩ := hfo.exists_pow_eq_one
    have hp : ((lamw w m : ℂˣ) : ℂ) ^ N = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hpow, map_one, Units.val_one]
    exact Complex.norm_eq_one_of_pow_eq_one hp hN.ne'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementUniformizerRatioDeterminant
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet


open _root_.Formalism.L2.Col in
theorem prod_diag_inv {E : Type} [Field E] [NumberField E] [StarRing E] (n : ℕ) (π : 𝓞 E) (d : ℕ) (hd : d ≤ n) :
    ∏ i : Fin n, (mhlDiag n π d i)⁻¹ = (mhlA π)⁻¹ ^ d := by
  have h1 : ∀ i : Fin n, (mhlDiag n π d i)⁻¹ = (fun j : ℕ => if j < d then (mhlA π)⁻¹ else 1) i.1 := by
    intro i
    unfold mhlDiag
    by_cases h : i.1 < d <;> simp [h]
  rw [Finset.prod_congr rfl fun i _ => h1 i, Fin.prod_univ_eq_prod_range (fun j : ℕ => if j < d then (mhlA π)⁻¹ else 1) n,
    Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  have : (Finset.range n).filter (fun j => j < d) = Finset.range d := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

theorem idem_mul_pow {R : Type} [CommRing R] {e : R} (hee : e * e = e) (x : R) (d : ℕ) : e * (e * x) ^ d = e * x ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, pow_succ, ← mul_assoc, ih]
    rw [show e * x ^ d * (e * x) = (e * e) * (x ^ d * x) by ring, hee]

theorem pow_mem_int {D : D7} {x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (d : ℕ) :
    x ^ d ∈ intAE D := by
  induction d with
  | zero => rw [pow_zero]; exact GlobalTheory.HeckeConj.one_mem_intAE D
  | succ d ih => rw [pow_succ]; exact GlobalTheory.HeckeConj.mul_mem_intAE D ih hx

theorem unit_mem {D : D7} {e a : Formalism.L2.Theta.AE D} (hee : e * e = e) (ha : finPart D (e * a) ∈ intAE D) (d : ℕ) :
    finPart D (e * a ^ d + (1 - e)) ∈ intAE D := by
  have he : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  rw [← idem_mul_pow hee a d, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, RingHom.map_mul, RingHom.map_pow]
  exact add_mem (GlobalTheory.HeckeConj.mul_mem_intAE D he (pow_mem_int ha d)) (sub_mem (GlobalTheory.HeckeConj.one_mem_intAE D) he)

theorem det_castGL {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (g : GL (Fin m) R) :
    Matrix.GeneralLinearGroup.det (castGL h g) = Matrix.GeneralLinearGroup.det g := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, castGL, Matrix.det_reindex_self]

theorem det_fin {D : D7} (V : HSp D) (α : GA D V) : finPart D (Formalism.L2.Theta.mt V α).det = (finHom V α).val.det := by
  rw [RingHom.map_det]; rfl

theorem det_swap {D : D7} {m : ℕ} (g : GL (Fin m) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) :
    swapAE D g.val.det = (Formalism.UG.bc (swapAE D) g).val.det := by
  rw [RingHom.map_det]; rfl

theorem det_cast {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (g : GL (Fin m) R) : (castGL h g).val.det = g.val.det := by
  have := congrArg Units.val (det_castGL h g)
  simpa only [Matrix.GeneralLinearGroup.val_det_apply] using this

theorem det_conj_inv {R : Type} [CommRing R] {n : ℕ} (C η : GL (Fin n) R) : ((C * η * C⁻¹)⁻¹).val.det = (η⁻¹).val.det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply]
  congr 1
  rw [map_inv, map_inv, map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

theorem cast_inv {D : D7} (V : HSp D) {n : ℕ} (h : n = V.rank) (α : GA D V) :
    castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α⁻¹)) = (castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)))⁻¹ := by
  rw [map_inv (finHom V) α, map_inv (Formalism.UG.bc (swapAE D)), map_inv (castGL h.symm)]

end GlobalTheory.Mem.R3.LiftBrg.EtaDet

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

theorem det_transport {D : D7} (V : HSp D) {n : ℕ} (h : n = V.rank) (α : GA D V) (C η : GL (Fin n) (Formalism.IndefR.Lev.EAf D))
    (hC : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * η * C⁻¹) :
    swapAE D (finPart D (Formalism.L2.Theta.mt V α⁻¹).det) = (η⁻¹).val.det := by
  have hg : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α⁻¹)) = (C * η * C⁻¹)⁻¹ := by
    rw [cast_inv V h α, hC]
  rw [det_fin V α⁻¹, det_swap (finHom V α⁻¹), ← det_cast h.symm (Formalism.UG.bc (swapAE D) (finHom V α⁻¹)), hg,
    det_conj_inv C η]

theorem prV_det_eta {D : D7} (n : ℕ) [NeZero n] (v : HeightOneSpectrum (𝓞 D.host.F)) {π : 𝓞 D.host.E} (hπ0 : π ≠ 0)
    (d : ℕ) :
    Formalism.UG.prV v ((((Formalism.L2.Col.mhlEta D.sp.cm n v hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) :
      GL (Fin n) (Formalism.IndefR.Lev.EAf D))⁻¹).val.det -
        Formalism.L2.Col.iA D.host.F D.host.E (∏ k : Fin n, (Formalism.L2.Col.mhlDiag n π d k)⁻¹)) = 0 := by
  have hdiag : ∀ i j : Fin n, Formalism.UG.prV v ((((Formalism.L2.Col.mhlEta D.sp.cm n v hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) :
      GL (Fin n) (Formalism.IndefR.Lev.EAf D))⁻¹).val i j) =
      Formalism.UG.prV v ((Matrix.diagonal fun k => Formalism.L2.Col.iA D.host.F D.host.E (Formalism.L2.Col.mhlDiag n π d k)⁻¹) i j) := by
    intro i j
    rw [Formalism.L2.Col.mhl_prV_eta_inv, Matrix.diagonal_apply]
    by_cases hij : i = j <;> simp [hij]
  have hm : (Formalism.UG.prV v).mapMatrix (((Formalism.L2.Col.mhlEta D.sp.cm n v hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) :
      GL (Fin n) (Formalism.IndefR.Lev.EAf D))⁻¹).val =
      (Formalism.UG.prV v).mapMatrix (Matrix.diagonal fun k => Formalism.L2.Col.iA D.host.F D.host.E (Formalism.L2.Col.mhlDiag n π d k)⁻¹) :=
    Matrix.ext hdiag
  rw [RingHom.map_sub, RingHom.map_det, hm, ← RingHom.map_det, Matrix.det_diagonal,
    map_prod (Formalism.L2.Col.iA D.host.F D.host.E), sub_self]

end GlobalTheory.Mem.R3.LiftBrg.EtaDet

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

theorem hom_mul_pow {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) (d : ℕ) :
    f ((a * b) ^ d) = f a ^ d * f b ^ d := by
  rw [map_pow, map_mul, mul_pow]

theorem final_alg {R : Type} [CommRing R] {e Δ c X W : R} (hee : e * e = e) (key : e * Δ = e * c) (hc : c = X * W) :
    e * Δ = e * W * (e * X + (1 - e)) := by
  linear_combination key + e * hc + (W - W * X) * hee

theorem swap_inj {D : D7} {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (h : swapAE D x = swapAE D y) :
    x = y :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective h

theorem idem_eq_of_swap {D : D7} {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {x c : Formalism.L2.Theta.AE D}
    (h : swapAE D (finPart D e) * swapAE D (finPart D x) = swapAE D (finPart D e) * swapAE D (finPart D c)) :
    e * x = e * c := by
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · simp only [RingHom.map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul]
  · apply swap_inj
    rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul]
    exact h

end GlobalTheory.Mem.R3.LiftBrg.EtaDet

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

theorem det_clause : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), d ≤ n → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → (∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0) → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ →
    ∃ u u' : Formalism.L2.Theta.AE D, finPart D u ∈ intAE D ∧ finPart D u' ∈ intAE D ∧ e * u * u' = e ∧
      e * (mt V α⁻¹).det = e * incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E) ^ d * u := by
  intro D V n _ h v Pb Ut d e C α hd he hε hα hC
  have hπ0 : ((Ut.π : 𝓞 D.host.E) : D.host.E) ≠ 0 := Formalism.L2.Col.mhl_alg_ne Ut.hπ0
  have hee : e * e = e := he.1.1
  have hfe : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  have hinv : finPart D (e * incA D ((Ut.π : D.host.E))⁻¹) ∈ intAE D := by
    by_contra hc
    exact Ut.hπP ((he.2 Ut.π Ut.hπ0).2 hc)
  have hpi : finPart D (e * incA D (Ut.π : D.host.E)) ∈ intAE D := by
    rw [RingHom.map_mul]
    exact GlobalTheory.HeckeConj.mul_mem_intAE D hfe (AddSubgroup.subset_closure ⟨1, fun v => one_mem _, Ut.π, rfl⟩)
  have hXY : incA D ((Ut.π : D.host.E))⁻¹ ^ d * incA D (Ut.π : D.host.E) ^ d = 1 := by
    rw [← mul_pow, ← RingHom.map_mul, inv_mul_cancel₀ hπ0, RingHom.map_one, one_pow]
  refine ⟨e * incA D ((Ut.π : D.host.E))⁻¹ ^ d + (1 - e), e * incA D (Ut.π : D.host.E) ^ d + (1 - e),
    unit_mem hee hinv d, unit_mem hee hpi d, ?_, ?_⟩
  · linear_combination e * hXY + ((e + 1) * (incA D ((Ut.π : D.host.E))⁻¹ ^ d * incA D (Ut.π : D.host.E) ^ d) -
      e * (incA D ((Ut.π : D.host.E))⁻¹ ^ d + incA D (Ut.π : D.host.E) ^ d) + (e - 1)) * hee
  ·
    have hdet := det_transport V h α C _ hC
    have hε' := hε _ (prV_det_eta (D := D) n v Ut.hπ0 d)
    rw [mul_sub, sub_eq_zero, prod_diag_inv n Ut.π d hd, Formalism.L2.Col.mhlA_inv Ut, ← hdet] at hε'
    have key : e * (Formalism.L2.Theta.mt V α⁻¹).det = e * incA D ((((Ut.π : D.host.E))⁻¹ *
        ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) ^ d) :=
      idem_eq_of_swap he.1 hε'
    have hc : incA D ((((Ut.π : D.host.E))⁻¹ * ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) ^ d) =
        incA D ((Ut.π : D.host.E))⁻¹ ^ d * incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E) ^ d :=
      hom_mul_pow (incA D) _ _ d
    exact final_alg hee key hc

end GlobalTheory.Mem.R3.LiftBrg.EtaDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfRationalUnitaryAdelicMul
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

noncomputable section
namespace GlobalTheory.Mem.Col2.RatMove

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ}


omit [NumberField E] [StarRing E] in
theorem glEquiv_apply_mulVec (g : GL (Fin n) E) (x : Sp E n) : Formalism.UG.glEquiv g x = (g : Matrix (Fin n) (Fin n) E) *ᵥ x := by
  simp [Formalism.UG.glEquiv]

theorem ufGL_eq (γ : UF E n) : ufGL E n γ = (((ratEquiv hc n).symm γ : URat hc n) : GL (Fin n) E) := by
  have hγ : ratHom hc n ((ratEquiv hc n).symm γ) = γ := (ratEquiv hc n).apply_symm_apply γ
  apply Units.ext
  refine Matrix.ext_of_mulVec_single fun j => ?_
  funext i
  have h1 := congrArg (fun g : UF E n => (g : Sp E n ≃ₗ[E] Sp E n) (Pi.single j 1) i) hγ
  simp only [ratHom, MonoidHom.coe_mk, OneHom.coe_mk] at h1
  rw [← glEquiv_apply_mulVec, ← glEquiv_apply_mulVec, h1]
  show Formalism.UG.glEquiv (toGLm E n γ.1) _ i = _
  rw [glEquiv_toGLm]


omit [NumberField E] [StarRing E] in
theorem glEquiv_symm_apply (γ : GL (Fin n) E) (v : Sp E n) :
    (Formalism.UG.glEquiv γ).symm v = ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v := by
  rw [LinearEquiv.symm_apply_eq]
  simp [Formalism.UG.glEquiv, Matrix.mulVec_mulVec]

theorem pullV_ratMul (γ : GL (Fin n) E) (g : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (Formalism.UG.bc (iA F E) γ * g) x = GlobalTheory.Mem.Col2.pullV g ((Formalism.UG.glEquiv γ).symm x) := by
  have h := Formalism.L2.Col.pullV_rawSm γ g 1 x
  rw [inv_one, mul_one, Units.val_one, Matrix.one_mulVec] at h
  rw [glEquiv_symm_apply]
  exact h

variable {hc} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem isPtOf_ratMul (γ : URat hc n) {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) :
    IsPtOf hc (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * g)
      (((ratHom hc n γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
  have hspan : Submodule.span E (p.deco.1.N : Set (Sp E n)) = ⊤ := by
    let L := p.deco.1.N
    let W := Submodule.span E (L : Set (Sp E n))
    change W = ⊤
    by_contra hW
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let f : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
    have hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) L := p.deco.2.uni
    have hsmul (a : E) : a • e x ∈ L := by
      rw [← hu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let i : E →ₗ[𝓞 E] L :=
      ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
    let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr p.deco.2.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := by
    rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg) hspan]
    ext w
    refine (h.lat _).symm.trans ?_
    show _ ↔ ((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ _ ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  have hst : (1 : GL (Fin n) (AfE F E))⁻¹ ∈
      Formalism.UG.stabGL (Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n)) := by
    rw [inv_one]; exact one_mem _
  have hN2 := Formalism.UG.P.global_lattice_equiv_holds F E (Fin n) (stdLat E n) γ g _ hst
  rw [inv_one, mul_one] at hN2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (ratIn hc n γ).2 h.uni
  · have hc2 := PtExist.carries_globLat (F := F) (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * g)
    rw [hN2, hN] at hc2
    exact hc2
  · intro P x hx i hi
    have hx' : (Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x ∈ p.deco.1.N := (mem_gmap _ _ _).1 hx
    rw [pullV_ratMul]
    exact h.f P _ hx' i hi
  · intro w x hx i
    have hx' : (Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x ∈ p.deco.1.N := (mem_gmap _ _ _).1 hx
    show HasRes w.1 _ (((((1 : GLG (E := E) (n := n) (SG := SG)) w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) *ᵥ
      p.deco.1.be w ((Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x)) i)
    rw [Pi.one_apply, Units.val_one, Matrix.one_mulVec, pullV_ratMul]
    exact h.be w _ hx' i
  · intro P i j
    show _ = algebraMap E _ ((Formalism.UG.glEquiv (γ : GL (Fin n) E) * p.fr P * (((1 : GLQ E n Q) P)⁻¹).1) (Pi.single j 1) i)
    have e1 : (((1 : GLQ E n Q) P)⁻¹).1 = 1 := by simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, mul_one, LinearEquiv.mul_apply, glEquiv_apply_mulVec, Units.val_mul, Matrix.mul_apply, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h.fr P l j]
    congr 1
    show adAt F P.1 (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((γ : GL (Fin n) E) i l)) = _
    rw [adAt_inclE]

theorem isPtOf_ratAd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (γ : UF E n) (g : GL (Fin n) (AfE F E))
    (p : DecoF E n ST SG Q), IsPtOf hc g p →
      IsPtOf hc (ratAd F γ * g) (((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
  intro F E _ _ _ _ _ _ hc n ST SG Q γ g p h
  have hγ : ratHom hc n ((ratEquiv hc n).symm γ) = γ := (ratEquiv hc n).apply_symm_apply γ
  have hR : ratAd F γ = Formalism.UG.bc (iA F E) ((((ratEquiv hc n).symm γ : URat hc n)) : GL (Fin n) E) := by
    show Formalism.UG.bc (iA F E) (ufGL E n γ) = _
    rw [ufGL_eq hc]
  have := isPtOf_ratMul ((ratEquiv hc n).symm γ) (ST := ST) (SG := SG) (Q := Q) h
  rw [hγ] at this
  rw [hR]
  exact this

end GlobalTheory.Mem.Col2.RatMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KsCondExact
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KsExactCond

theorem ksCond_exact : RayField → PrincipalIdealSt → CMCurveGoodOutsidePrimeSt →
    V4.KsCond fun B f => ∃ δ : FieldDat B.toPre, B.KsExact δ f := by
  intro hR hP hA
  refine ⟨Col2.InEx.ev_of_forall fun K B₀ f₀ S₁ S₂ hO s1 s2 => ?_, fun B B' f f' e hf hS => ?_⟩
  · obtain ⟨δ⟩ := nonempty_fieldDat hR hA B₀.toPre
    obtain ⟨B₁, e₁, k⟩ := (GlobalTheory.Mem.KsBase.exists_base_listField hR hP _ f₀ δ).2
    obtain ⟨B₂, e₂, k₂, l₂⟩ := Inh.exists_fixed B₁ (S₁ B₁.KsC) (s1 _)
    obtain ⟨B, e, l₃⟩ := BaseEnl.exists_enl B₂ (S₂ B₁.KsC B₂.fixedCoefficientFieldInComplex) (s2 _ _)
    have hk : B.KsC = B₁.KsC := e.KsC_eq.trans k₂
    have e' : B.toPre = B₀.toPre := e.1.trans (e₂.trans e₁)
    have hH : Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex) := by
      rw [hk, Has₂, e.fixedCoefficientField_eq]
      exact ⟨l₂, l₃⟩
    rw [← hk] at k
    clear e e₁ e₂ hO
    generalize B₀.toPre = P₀ at *
    subst e'
    exact ⟨B, f₀, rfl, HEq.rfl, ⟨δ, k⟩, hH⟩
  · have e' := e.1
    unfold Base.KsExact at hS ⊢
    rw [e.KsC_eq]
    clear e
    generalize B.KsC = F at *
    generalize B.toPre = P at *
    subst e'
    obtain rfl := eq_of_heq hf
    exact hS

end GlobalTheory.Mem.KsExactCond
end

