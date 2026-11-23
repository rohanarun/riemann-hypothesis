module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaNormUnimodularLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupModTypePrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.LevMod

open GlobalTheory.CongLevel

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))

def RedTo (g : Sp E n ≃ₗ[E] Sp E n) (hbar : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) : Prop :=
  ∀ x ∈ stdAt E n P, redV P (g x) = hbar.1.mulVec (redV P x)

variable {P}

theorem RedTo.one : RedTo P (1 : Sp E n ≃ₗ[E] Sp E n) 1 := fun x _ => by
  rw [Units.val_one, Matrix.one_mulVec]; rfl

theorem RedTo.mul {g g' : Sp E n ≃ₗ[E] Sp E n} {a b : GL (Fin n) (𝓞 E ⧸ P.asIdeal)} (hg' : g' ∈ GLint E n P)
    (h : RedTo P g a) (h' : RedTo P g' b) : RedTo P (g * g') (a * b) := fun x hx => by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← h' x hx]
  exact h _ ((hg' x).2 hx)

theorem RedTo.inv {g : Sp E n ≃ₗ[E] Sp E n} {a : GL (Fin n) (𝓞 E ⧸ P.asIdeal)} (hg : g ∈ GLint E n P)
    (h : RedTo P g a) : RedTo P g⁻¹ a⁻¹ := fun x hx => by
  have h1 := h _ (((inv_mem hg : g⁻¹ ∈ GLint E n P) x).2 hx)
  rw [show g (g⁻¹ x) = x from g.apply_symm_apply x] at h1
  rw [h1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]


variable (P) in
def redSub (G : Subgroup (Sp E n ≃ₗ[E] Sp E n)) (hG : G ≤ GLint E n P) : Subgroup (GL (Fin n) (𝓞 E ⧸ P.asIdeal)) where
  carrier := {a | ∃ g ∈ G, RedTo P g a}
  one_mem' := ⟨1, one_mem _, RedTo.one⟩
  mul_mem' := fun ⟨g, hg, h⟩ ⟨g', hg', h'⟩ => ⟨g * g', mul_mem hg hg', RedTo.mul (hG hg') h h'⟩
  inv_mem' := fun ⟨g, hg, h⟩ => ⟨g⁻¹, inv_mem hg, h.inv (hG hg)⟩

end Red

theorem unipotentArg_extendByIdOnLastCoords {E : Type} [Field E] {n : ℕ} (c : ℕ) (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    Loc.n1Arg (extE c κ) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [add_assoc, extE_apply, resX_eN]
  simp only [map_zero, sub_self, add_zero]
  unfold Loc.atN Loc.eN
  split_ifs with h1 h2
  · exact absurd h2 (by simp)
  · rfl
  · rfl

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem extE_mem_Cbe (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs)
    (hd : ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E))) (h : AutY X R j)
    (hh : h ∈ stabL X.E _ (lamYat (Pr := Pr) j w)) (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j))
    (hκ : κ ∈ GLint X.E (R.N j) w) (hr : ∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) :
    extE (cOf R j) κ ∈ Loc.Cbe (Jat (Pr := Pr) sharp j w) h := by
  have hq : ((qOf w : ℕ) : X.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero w
  unfold lamYat at hh
  rw [if_pos hw] at hh
  refine ⟨extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ κ, ?_⟩
  have e : (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ) = h⁻¹ * extE (cOf R j) κ * h := by simp
  show (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ) ∈ Jat (Pr := Pr) sharp j w
  rw [e]
  have hs := mul_mem (mul_mem (inv_mem hh) (extE_stab w (qOf w) (cOf R j) (fun i => i + 1) κ hκ)) hh
  have hc := conj_cong (qOf w) _ _ h hh (extE_cong w (qOf w) (cOf R j) (fun i => i + 1) hd κ hκ hr)
  unfold Jat
  rw [if_pos hw]
  split_ifs
  · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact CongLevel.sclLat_le w _ hq _ _ _
    · exact smul_mem_sclLat w _ hq _ _ _ x hx
    · exact bvec_mem w _ hq _ _ _
  · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact CongLevel.sclLat_le w _ hq _ _ _
    · exact smul_mem_sclLat w _ hq _ _ _ x hx
    · exact bvec_mem w _ hq _ _ _

theorem exists_levG : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j), cst.Ok → P.1 ∈ Pr.vGs → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) → prCat (Pr := Pr) cst.sharp j P.1 h ≤ GLint X.E (R.N j) P.1 → (∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P.1, y x ∈ lamYat (Pr := Pr) (R := R) j P.1) → lamRow Ch mu cst.sharp j P.1 (LinearMap.id + (qOf P.1 : X.E) • y) = 1) → ChiMul Ch sel mu cst j P h → ChiTriv Ch sel mu cst j P h → ∃ lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j), GrpG sel mu cst j P h lev ∧ ChrG Ch sel mu cst j P h lev := by
  intro X Pr R Ch sel S mu cst j P h hc hP hdu hh hle hlam hmul htriv
  have hq : ((qOf P.1 : ℕ) : X.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
  have hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)) := fun a ha h0 => by
    have := GlobalTheory.TypePrimeUnif.intAt_div_of_notMem_sq P.1 _ (Ideal.absNorm_mem _) hdu.2 a ha h0
    rwa [map_natCast] at this
  have hone : ∀ κ ∈ GLint X.E (R.N j) P.1, (∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (κ x) = redV P.1 x) →
      chiInv Ch sel mu cst j P h (extE (cOf R j) κ) = 1 := by
    intro κ hκ hr
    unfold lamYat at hh hlam
    rw [if_pos hP] at hh hlam
    have hcong := conj_cong (qOf P.1) _ _ h hh
      (extE_cong P.1 (qOf P.1) (cOf R j) (fun i => i + 1) hd κ hκ hr)
    have h1 := hlam ((qOf P.1 : X.E)⁻¹ • ((h⁻¹ * extE (cOf R j) κ * h : AutY X R j).toLinearMap - LinearMap.id))
      fun x hx => by
        have h2 := hcong x hx
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
        exact h2
    rw [smul_inv_smul₀ hq, add_sub_cancel] at h1
    unfold chiInv
    rw [h1, unipotentArg_extendByIdOnLastCoords, hc.psi_int P 0 (by simpa using CongLevel.intAt_nat P.1 0), inv_one, one_mul]
  obtain ⟨lam, hl⟩ := exists_char (H := ↥(redSub P.1 _ hle)) (CAt sel mu cst j P h) (chiInv Ch sel mu cst j P h)
    (fun r a => ∃ g ∈ GLint X.E (R.N j) P.1,
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) ∧ RedTo P.1 g a.1)
    hmul.1 hmul.2
    (fun ⟨a, g, hg, hga⟩ => by
      obtain ⟨r, hr, hrg⟩ := id hg
      exact ⟨r, hr, g, hle hg, hrg, hga⟩)
    (by
      rintro r a r' a' ⟨g, hg, h1, h2⟩ ⟨g', hg', h1', h2'⟩
      refine ⟨g * g', mul_mem hg hg', fun x => ?_, RedTo.mul hg' h2 h2'⟩
      show r (r' _) = _
      rw [h1', h1]
      rfl)
    (by
      rintro a r hr r' hr' ⟨g, hg, h1, h2⟩ ⟨g', hg', h1', h2'⟩
      have hκ : g⁻¹ * g' ∈ GLint X.E (R.N j) P.1 := mul_mem (inv_mem hg) hg'
      have hred : ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 ((g⁻¹ * g') x) = redV P.1 x := fun x hx => by
        rw [RedTo.mul hg' (h2.inv hg) h2' x hx, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      have hs : extE (cOf R j) (g⁻¹ * g') ∈ CAt sel mu cst j P h := extE_mem_Cbe _ j P.1 hP hd h hh _ hκ hred
      have ht : (extE (cOf R j) (g⁻¹ * g'))⁻¹ * (r⁻¹ * r') ∈ CAt sel mu cst j P h :=
        mul_mem (inv_mem hs) (mul_mem (inv_mem hr) hr')
      have ht1 := htriv _ ht fun x => by
        show (extE (cOf R j) (g⁻¹ * g')).symm (r.symm (r' _)) = _
        rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq, extE_inX, h1, h1']
        exact congrArg _ (g.apply_symm_apply _).symm
      have e : r' = r * (extE (cOf R j) (g⁻¹ * g') * ((extE (cOf R j) (g⁻¹ * g'))⁻¹ * (r⁻¹ * r'))) := by
        rw [mul_inv_cancel_left, mul_inv_cancel_left]
      have h3 := hmul.2 r hr _ (mul_mem hs ht)
      rw [← e, hmul.2 _ hs _ ht, ht1, hone _ hκ hred, mul_one, mul_one] at h3
      exact h3.symm)
  exact ⟨⟨redSub P.1 _ hle, lam⟩, fun _ => Iff.rfl,
    fun a g r hr h1 h2 => hl a r hr ⟨g, hle ⟨r, hr, h1⟩, h1, h2⟩⟩

end GlobalTheory.Mem.Col2.LevMod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodPairBaseLat
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.Per.ConjCM

open GlobalTheory.ConjPoint

variable {R : Ranks} (H : Host R)

theorem mem_baseLat (w : ℂ) :
    w ∈ baseLat H ↔ ∃ c ∈ H.ccK, w = H.φ₀ (((c : H.K) : H.E)) := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, H.ccK.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', H.ccK.add_mem hc hc', by simp⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, H.ccK.neg_mem hc, by simp⟩
  · exact fun hw => AddSubgroup.subset_closure hw

theorem exists_periodPair_baseLat : ∃ L : PeriodPair, ∀ z, z ∈ baseLat H ↔ z ∈ L.lattice := by
  have hr : Module.finrank ℚ H.K = 2 :=
    Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos (H.sqd_sq)
  have hd : NumberField.discr H.K = -(H.d : ℤ) :=
    GlobalTheory.discr_eq_neg_of_sq_eq hr H.hyp.2.1.squarefree
      (by have := H.hyp.2.2.2.1; omega)
      (Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq))
  let σ : H.K →+* ℂ := H.φ₀.comp H.K.val.toRingHom
  let I : (Ideal (𝓞 H.K))⁰ := ⟨H.ccK, mem_nonZeroDivisors_of_ne_zero H.ccK_ne_bot⟩
  obtain ⟨L, hL⟩ := GlobalTheory.QuadraticZeta.exists_periodPair hr hd σ (FractionalIdeal.mk0 H.K I)
  refine ⟨L, fun z => ?_⟩
  rw [mem_baseLat, ← SetLike.mem_coe (p := L.lattice), hL]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(c : H.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨c, hc, rfl⟩

end GlobalTheory.Mem.Per.ConjCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSetPosFinite
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolUnique

theorem haar_eq_of_eq_on_set {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ μ' : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure] (S : Set G) (h : μ S = μ' S)
    (h0 : μ' S ≠ 0) (ht : μ' S ≠ ⊤) : μ = μ' := by
  have hμ := Measure.isMulLeftInvariant_eq_smul μ μ'
  have hc : ((Measure.haarScalarFactor μ μ' : NNReal) : ENNReal) = 1 := by
    have h1 : μ S = (Measure.haarScalarFactor μ μ' : ENNReal) * μ' S := by
      conv_lhs => rw [hμ]
      simp
    rw [h] at h1
    exact ((ENNReal.mul_left_inj h0 ht).1 (by rw [one_mul]; exact h1)).symm
  have hc' : Measure.haarScalarFactor μ μ' = 1 := by exact_mod_cast hc
  rw [hμ, hc', one_smul]

theorem exists_set_pos_finite (cd : CDHaar) (P Q : ℕ) :
    ∃ B : Set (UpqT P Q), MeasurableSet B ∧ cd.cd P Q B ≠ 0 ∧ cd.cd P Q B ≠ ⊤ := by
  obtain ⟨_, _, _, _, _, _⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  haveI := cd.haar P Q
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : UpqT P Q)
  exact ⟨K, hK.measurableSet, (Measure.measure_pos_of_mem_nhds _ hK1).ne', hK.measure_lt_top.ne⟩

theorem volMeas_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → ∀ μ μ', IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ → IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ' → μ = μ' := by
  intro F E _ _ _ _ _ _ cm I _ τ cd W _ _ μ μ' hμ hμ'
  obtain ⟨hH, ⟨θ, hθ⟩, hall⟩ := hμ
  obtain ⟨hH', -, hall'⟩ := hμ'
  obtain ⟨⟨A, hA⟩, hB⟩ := hall θ hθ
  have hB' := (hall' θ hθ).2 A hA
  have hB := hB A hA
  choose B hBm hB0 hBt using fun ρ : I => exists_set_pos_finite cd (W.sig (τ ρ)).1 (W.sig (τ ρ)).2
  obtain ⟨_, _, _⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E cm.sig W.rank W.gram
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) cm.sig W.gram) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF F) cm.sig W.gram))
  haveI : BorelSpace (HA (AF F) cm.sig W.gram) := ⟨rfl⟩
  refine haar_eq_of_eq_on_set μ μ' _ ((hB B hBm).trans (hB' B hBm).symm) ?_ ?_
  · rw [hB' B hBm]
    exact Finset.prod_ne_zero_iff.2 fun ρ _ => hB0 ρ
  · rw [hB' B hBm]
    exact ENNReal.prod_ne_top fun ρ _ => hBt ρ

end GlobalTheory.Mem.VolUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionParamLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.TorsionDegree

theorem exists_torsion_param_lattice (L : PeriodPair) (n : ℕ) [NeZero n] :
    ∃ t : (Fin 2 → ZMod n) →+ (latticeCurve L).toAffine.Point, Function.Injective t ∧
      ∀ P, n • P = 0 → ∃ v, t v = P := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  let f : ℂ → ℤ →+ (latticeCurve L).toAffine.Point := fun ω =>
    (latticePointHom L).comp (zmultiplesHom ℂ (ω / n))
  have hf : ∀ ω (a : ℤ), f ω a = latticePoint L (a * (ω / n)) := fun ω a => by
    simp [f]
  have h0 : ∀ ω ∈ L.lattice, f ω n = 0 := fun ω hω => by
    rw [hf, latticePoint_eq_zero_iff]
    convert hω using 1
    push_cast
    field_simp
  let t : (Fin 2 → ZMod n) →+ (latticeCurve L).toAffine.Point :=
    (ZMod.lift n ⟨f L.ω₁, h0 _ L.ω₁_mem_lattice⟩).comp (Pi.evalAddMonoidHom (fun _ => ZMod n) 0) +
    (ZMod.lift n ⟨f L.ω₂, h0 _ L.ω₂_mem_lattice⟩).comp (Pi.evalAddMonoidHom (fun _ => ZMod n) 1)
  have ht : ∀ a b : ℤ, t ![(a : ZMod n), (b : ZMod n)] = latticePoint L ((a * L.ω₁ + b * L.ω₂) / n) := by
    intro a b
    simp only [t, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, ZMod.lift_coe, hf]
    rw [← latticePoint_add]
    congr 1
    ring
  refine ⟨t, (injective_iff_map_eq_zero t).2 fun v hv => ?_, fun P hP => ?_⟩
  · obtain ⟨a, ha⟩ := ZMod.intCast_surjective (v 0)
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective (v 1)
    have e : v = ![(a : ZMod n), (b : ZMod n)] := by
      ext i; fin_cases i <;> simp [ha, hb]
    rw [e, ht, latticePoint_eq_zero_iff, PeriodPair.mem_lattice] at hv
    obtain ⟨c, d, hcd⟩ := hv
    have h1 : ((a - n * c : ℤ) : ℝ) • L.ω₁ + ((b - n * d : ℤ) : ℝ) • L.ω₂ = 0 := by
      rw [eq_div_iff hn'] at hcd
      simp only [Complex.real_smul]
      push_cast
      linear_combination -hcd
    obtain ⟨h2, h3⟩ := LinearIndependent.pair_iff.1 L.indep _ _ h1
    have h2' : a = n * c := by
      have : a - n * c = 0 := by exact_mod_cast h2
      omega
    have h3' : b = n * d := by
      have : b - n * d = 0 := by exact_mod_cast h3
      omega
    rw [e, h2', h3']
    ext i; fin_cases i <;> simp
  · obtain ⟨z, rfl⟩ := latticePoint_surjective L P
    have h1 : latticePoint L (n • z) = 0 := by
      rw [← latticePointHom_apply, map_nsmul, latticePointHom_apply]; exact hP
    rw [latticePoint_eq_zero_iff] at h1
    obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 h1
    refine ⟨_, (ht a b).trans ?_⟩
    rw [hab, nsmul_eq_mul, mul_div_cancel_left₀ _ hn']

theorem exists_torsion_param (W : WeierstrassCurve ℂ) [W.IsElliptic] (n : ℕ) [NeZero n] :
    ∃ t : (Fin 2 → ZMod n) →+ W.toAffine.Point, Function.Injective t ∧
      ∀ P, n • P = 0 → ∃ v, t v = P := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_latticeCurve W
  let e := variableChangePointEquiv C hC
  obtain ⟨t, hi, hs⟩ := exists_torsion_param_lattice L n
  refine ⟨e.toAddMonoidHom.comp t, e.injective.comp hi, fun P hP => ?_⟩
  obtain ⟨v, hv⟩ := hs (e.symm P) (by rw [← map_nsmul, hP, map_zero])
  exact ⟨v, by simp [hv]⟩

theorem exists_linearEquiv {G G' : Type} [AddCommGroup G] [AddCommGroup G'] (n : ℕ) [NeZero n]
    (t : (Fin 2 → ZMod n) →+ G') (hi : Function.Injective t) (hs : ∀ P, n • P = 0 → ∃ v, t v = P)
    (ι φ : G →+ G') (hι : Function.Injective ι) (hφ : Function.Injective φ)
    (hr : ∀ P, n • P = 0 → ∃ Q, ι Q = P) :
    ∃ g : (Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n), ∀ v Q, ι Q = t v → φ Q = t (g v) := by
  have hv : ∀ v : Fin 2 → ZMod n, n • v = 0 := fun v => by
    ext i; simp
  have h1 : ∀ v, ∃ Q, ι Q = t v := fun v => hr _ (by rw [← map_nsmul, hv, map_zero])
  choose s hs' using h1
  have h2 : ∀ v, ∃ w, t w = φ (s v) := fun v => hs _ (by
    have : n • s v = 0 := hι (by rw [map_nsmul, hs', ← map_nsmul, hv, map_zero, map_zero])
    rw [← map_nsmul, this, map_zero])
  choose u hu using h2
  have hadd : ∀ v w, u (v + w) = u v + u w := fun v w => hi (by
    rw [map_add (f := _), hu, hu, hu, ← map_add (f := _)]
    congr 1
    exact hι (by rw [map_add (f := _), hs', hs', hs', map_add (f := _)]))
  let U := (AddMonoidHom.mk' u hadd).toZModLinearMap n
  have hU : Function.Injective U := fun v w h => hi (by
    have h' : u v = u w := h
    rw [← hs', ← hs', hφ ((hu v).symm.trans (h' ▸ hu w))])
  refine ⟨LinearEquiv.ofBijective U ⟨hU, Finite.surjective_of_injective hU⟩, fun v Q hQ => ?_⟩
  rw [hι (hQ.trans (hs' v).symm), ← hu]
  rfl

theorem card_linearEquiv (n : ℕ) :
    Nat.card ((Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)) = Nat.card (GL (Fin 2) (ZMod n)) :=
  Nat.card_congr (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)).symm.toEquiv

theorem finrank_adjoin_le {k : Type} [Field k] [CharZero k] [Algebra k ℂ] (A : WeierstrassCurve k) [A.IsElliptic]
    (n : ℕ) [NeZero n] [FiniteDimensional k (IntermediateField.adjoin k (torsionCoords (A.baseChange ℂ) n))] :
    Module.finrank k (IntermediateField.adjoin k (torsionCoords (A.baseChange ℂ) n)) ≤
      Nat.card (GL (Fin 2) (ZMod n)) := by
  classical
  set S := torsionCoords (A.baseChange ℂ) n with hS
  set M := IntermediateField.adjoin k S with hM
  have : (A.baseChange ℂ).IsElliptic := inferInstanceAs (A.map _).IsElliptic
  obtain ⟨t, hi, hs⟩ := exists_torsion_param (A.baseChange ℂ) n
  let m : (M →ₐ[k] ℂ) → (A.baseChange M).toAffine.Point →+ (A.baseChange ℂ).toAffine.Point :=
    fun φ => WeierstrassCurve.Affine.Point.map (W' := A.toAffine) φ
  have hm : ∀ φ, Function.Injective (m φ) := fun φ => WeierstrassCurve.Affine.Point.map_injective φ
  have hpt : ∀ (x y : ℂ) (h : (A.baseChange ℂ).toAffine.Nonsingular x y) (hx : x ∈ M) (hy : y ∈ M),
      (A.baseChange M).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩ := fun x y h hx hy =>
    (A.toAffine.baseChange_nonsingular (f := M.val) M.val.injective ⟨x, hx⟩ ⟨y, hy⟩).mp h
  have hr : ∀ P, n • P = 0 → ∃ Q, m M.val Q = P := by
    rintro (_ | ⟨x, y, h⟩) hP
    · exact ⟨0, rfl⟩
    · exact ⟨.some _ _ (hpt x y h (IntermediateField.subset_adjoin k S ⟨x, y, h, hP, Or.inl rfl⟩)
        (IntermediateField.subset_adjoin k S ⟨x, y, h, hP, Or.inr rfl⟩)), rfl⟩
  choose g hg using fun φ => exists_linearEquiv n t hi hs (m M.val) (m φ) (hm _) (hm φ) hr
  have hginj : Function.Injective g := by
    intro φ ψ h
    refine IntermediateField.algHom_ext_of_eq_adjoin k hM ?_
    rintro z ⟨x, y, hxy, h0, hz⟩
    obtain ⟨v, hv⟩ := hs _ h0
    have hx := IntermediateField.subset_adjoin k S ⟨x, y, hxy, h0, Or.inl rfl⟩
    have hy := IntermediateField.subset_adjoin k S ⟨x, y, hxy, h0, Or.inr rfl⟩
    have e : m φ (.some _ _ (hpt x y hxy hx hy)) = m ψ (.some _ _ (hpt x y hxy hx hy)) := by
      rw [hg φ v _ hv.symm, hg ψ v _ hv.symm, h]
    have e' := WeierstrassCurve.Affine.Point.some.inj e
    rcases hz with rfl | rfl
    · exact e'.1
    · exact e'.2
  rw [← card_linearEquiv, ← AlgHom.card k M ℂ, ← Nat.card_eq_fintype_card]
  have : Finite ((Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := (Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)))
  exact Nat.card_le_card_of_injective g hginj

theorem finrank_sup_adjoin {K L : Type} [Field K] [Field L] [Algebra K L] (H : IntermediateField K L) (S : Set L)
    [FiniteDimensional K H] [FiniteDimensional H (IntermediateField.adjoin H S)] :
    FiniteDimensional K (H ⊔ IntermediateField.adjoin K S : IntermediateField K L) ∧
      Module.finrank K (H ⊔ IntermediateField.adjoin K S : IntermediateField K L) =
        Module.finrank K H * Module.finrank H (IntermediateField.adjoin H S) := by
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup]
  have : IsScalarTower K H (IntermediateField.adjoin H S) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Free H (IntermediateField.adjoin H S) := Module.Free.of_divisionRing _ _
  have : Module.Free K H := Module.Free.of_divisionRing _ _
  have h : FiniteDimensional K (IntermediateField.adjoin H S) := Module.Finite.trans H _
  exact ⟨h,
    (Module.finrank_mul_finrank K H (IntermediateField.adjoin H S)).symm⟩

theorem finrank_torsionField_le : ∀ (d : ℕ) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (A : WeierstrassCurve F) [A.IsElliptic], FiniteDimensional ℚ (torsionField d A) ∧ Module.finrank ℚ (torsionField d A) ≤ Module.finrank ℚ (hilbertField d F) * Nat.card (GL (Fin 2) (ZMod 12)) := by
  intro d F _ A _
  have hint : IsIntegral ℚ (sqrtNegNat d) :=
    IsIntegral.of_pow (n := 2) (by norm_num) (by
      rw [sqrtNegNat_sq]
      exact (isIntegral_natCast d).neg)
  have : FiniteDimensional ℚ ℚ⟮sqrtNegNat d⟯ := IntermediateField.adjoin.finiteDimensional hint
  have hH : FiniteDimensional ℚ (hilbertField d F) := by
    unfold hilbertField; infer_instance
  set H := hilbertField d F with hHdef
  let A' : WeierstrassCurve H := A.map (IntermediateField.inclusion (le_sup_right : F ≤ H)).toRingHom
  have hA : A'.baseChange ℂ = A.baseChange ℂ := by
    simp only [A', WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
    rfl
  have : (A.baseChange ℂ).IsElliptic := inferInstanceAs (A.map _).IsElliptic
  have : A'.IsElliptic := by
    simp only [A']
    exact WeierstrassCurve.instIsEllipticMap _ _
  have hfin := finite_torsionCoords (A.baseChange ℂ) 12 (by norm_num)
  have halg := FieldsEx.isAlgebraic_of_torsionCoords_finite F A 12 hfin
  have : Finite (torsionCoords (A'.baseChange ℂ) 12) := hA ▸ hfin.to_subtype
  have hM : FiniteDimensional H (IntermediateField.adjoin H (torsionCoords (A'.baseChange ℂ) 12)) :=
    IntermediateField.finiteDimensional_adjoin fun z hz => (halg z (hA ▸ hz)).isIntegral.tower_top
  have hle := finrank_adjoin_le A' 12
  obtain ⟨h1, h2⟩ := finrank_sup_adjoin H (torsionCoords (A'.baseChange ℂ) 12)
  have e : torsionField d A = H ⊔ IntermediateField.adjoin ℚ (torsionCoords (A'.baseChange ℂ) 12) := by
    rw [hA]
    rfl
  rw [e]
  exact ⟨h1, h2.le.trans (Nat.mul_le_mul_left _ hle)⟩

end GlobalTheory.Mem.TorsionDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeNormalFormViaMatrix
section
noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal

theorem nfMat_eq_qnf {E : Type} [Field E] (n c : ℕ) (q : E) (e : Fin c → ℤ) (z : Fin n → E) :
    nfMat n c q e z = GlobalTheory.QNF.nfMat n c q e z := by
  funext l s
  unfold nfMat GlobalTheory.QNF.nfMat
  by_cases hs : s.1 < n
  · simp [hs]
  · by_cases hls : l = s
    · subst hls
      simp [hs, Loc.inX]
    · by_cases hn : s.1 = n
      · by_cases hl : l.1 < n
        · simp [hls, hn, hl, Loc.inX]
        · simp [hls, hn, hl, Loc.inX]
      · simp [hs, hls, hn]

theorem nf_matrix : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h → ∃ (e : Fin (cOf R j) → ℤ) (z : Fin (R.N j) → X.E), (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (fun l : Fin (R.N j + cOf R j) => if hl : l.1 < R.N j then z ⟨l.1, hl⟩ else 0) ∈ lamYat (Pr := Pr) (R := R) j P ∧ (lamYat (Pr := Pr) (R := R) j P).map (h.toLinearMap.restrictScalars (𝓞 X.E)) = (lamYat (Pr := Pr) (R := R) j P).map ((Matrix.toLin' (nfMat (R.N j) (cOf R j) (qOf P : X.E) e z)).restrictScalars (𝓞 X.E)) := by
  intro X Pr R j P hP h hh
  obtain ⟨e, z, h1, h2, h3⟩ := (GlobalTheory.QNF.nf_iff_matNF X Pr R j P hP h).1 hh
  exact ⟨e, z, h1, h2, by rw [nfMat_eq_qnf]; exact h3⟩

end GlobalTheory.Mem.Col2.IdxEx

end
end

