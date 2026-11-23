module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.HasCompactSupportOfSection
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical ComplexConjugate

namespace PositivityTheory.Rg.BcB.CG

theorem trace_mul_ent {n : ℕ} (M : KMod n) (A B : M.V →L[ℂ] M.V) :
    LinearMap.trace ℂ M.V ((A * B : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V) = ∑ i, ∑ j, ent M A i j * ent M B j i := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ M.V)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ((A * B : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V) (stdOrthonormalBasis ℂ M.V i) =
      A (∑ j, inner ℂ (stdOrthonormalBasis ℂ M.V j) (B (stdOrthonormalBasis ℂ M.V i)) • stdOrthonormalBasis ℂ M.V j) := by
    rw [(stdOrthonormalBasis ℂ M.V).sum_repr']; rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right, ent, ent, mul_comm]

theorem phiOf_eq {n : ℕ} (M : KMod n) (Tθ : M.V →L[ℂ] M.V) (k : Mat n → (M.V →L[ℂ] M.V)) (y : G n) :
    phiOf M Tθ k y = ∑ p, ∑ q, ent M (k y.val) p q * ent M Tθ q p :=
  trace_mul_ent M _ _

theorem ent_adjoint {n : ℕ} (M : KMod n) [CompleteSpace M.V] (A : M.V →L[ℂ] M.V) (i j : Ix M) :
    ent M (ContinuousLinearMap.adjoint A) i j = conj (ent M A j i) := by
  simp only [ent]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

theorem sum_pair {α β : Type} [Fintype α] [Fintype β] (X : α → α → ℂ) (Y : β → β → ℂ) :
    ∑ i : α × β, ∑ j : α × β, X i.1 j.1 * Y i.2 j.2 = (∑ p, ∑ q, X p q) * ∑ p, ∑ q, Y p q := by
  simp only [Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem sum_io {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ] (A A' : α → α → ℂ) (B B' : β → β → ℂ)
    (C D : κ → κ → ℂ) :
    ∑ i : (α × β) × κ, ∑ j : (α × β) × κ,
        A i.1.1 j.1.1 * B i.1.2 j.1.2 * C i.2 j.2 * (A' j.1.1 i.1.1 * B' j.1.2 i.1.2 * D j.2 i.2) =
      (∑ p, ∑ q, A p q * A' q p) * (∑ p, ∑ q, B p q * B' q p) * ∑ x, ∑ y, C x y * D y x := by
  calc _ = ∑ i : (α × β) × κ, ∑ j : (α × β) × κ,
          (A i.1.1 j.1.1 * A' j.1.1 i.1.1 * (B i.1.2 j.1.2 * B' j.1.2 i.1.2)) * (C i.2 j.2 * D j.2 i.2) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ p : α × β, ∑ q : α × β, A p.1 q.1 * A' q.1 p.1 * (B p.2 q.2 * B' q.2 p.2)) * ∑ x, ∑ y, C x y * D y x :=
        sum_pair (fun p q : α × β => A p.1 q.1 * A' q.1 p.1 * (B p.2 q.2 * B' q.2 p.2)) (fun x y => C x y * D y x)
    _ = _ := by
        rw [sum_pair (fun p q => A p q * A' q p) (fun p q => B p q * B' q p)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

theorem prod_sum_ent (M : Mods E n) (A B : Ops M) :
    ∏ v, (∑ p, ∑ q, ent (M v) (A v) p q * ent (M v) (B v) q p) =
      ∑ P : IxA M, ∑ Q : IxA M, (∏ v, ent (M v) (A v) (P v) (Q v)) * ∏ v, ent (M v) (B v) (Q v) (P v) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun Q _ => ?_
  exact Finset.prod_mul_distrib

theorem tensTr : TensTr := by
  intro E _ _ _ a b Ma Mb κ _ ka kb Ta Tb ψ N g
  have ha := prod_sum_ent Ma (fun v => ka v (gInf v g.1).val) Ta
  have hb := prod_sum_ent Mb (fun v => kb v (gInf v g.2).val) Tb
  simp only [F.trM, tens, opM, entA, phiOf_eq]
  rw [ha, hb]
  exact sum_io (α := IxA Ma) (β := IxA Mb) (κ := κ)
    (fun P Q : IxA Ma => ∏ v, ent (Ma v) (ka v (gInf v g.1).val) (P v) (Q v))
    (fun Q P : IxA Ma => ∏ v, ent (Ma v) (Ta v) (Q v) (P v))
    (fun P Q : IxA Mb => ∏ v, ent (Mb v) (kb v (gInf v g.2).val) (P v) (Q v))
    (fun Q P : IxA Mb => ∏ v, ent (Mb v) (Tb v) (Q v) (P v)) (fun x y : κ => ψ x y (hFin g)) (fun y x : κ => N y x)

theorem gInf_eq (v : InfinitePlace E) (g : GA E n) :
    gInf v g = GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v)
      (GeneralLinearGroup.map (pInf E) g) := rfl

theorem continuous_hFin : Continuous (hFin (E := E) (a := a) (b := b)) :=
  ((_root_.GlobalTheory.GLProj.continuous_proj_incl E a).2.1.comp continuous_fst).prodMk ((_root_.GlobalTheory.GLProj.continuous_proj_incl E b).2.1.comp continuous_snd)

theorem hFin_inv (g : H E a b) : hFin g⁻¹ = (hFin g)⁻¹ :=
  Prod.ext (map_inv (gFin (E := E) (n := a)) g.1) (map_inv (gFin (E := E) (n := b)) g.2)

def ofComps (y : InfinitePlace E → G n) : GL (Fin n) (Cinf E) :=
  Units.map (Matrix.piRingEquiv (n := Fin n) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
    (MulEquiv.piUnits.symm y)

theorem continuous_ofComps : Continuous (ofComps (E := E) (n := n)) := by
  have hc : Continuous fun x : InfinitePlace E → Mat n =>
      (Matrix.piRingEquiv (n := Fin n) (β := fun _ : InfinitePlace E => ℂ)).symm x :=
    continuous_matrix fun i j => continuous_pi fun v => (continuous_apply v).matrix_elem i j
  exact (Continuous.units_map _ hc).comp (ContinuousMulEquiv.piUnits (M := fun _ : InfinitePlace E => Mat n)).symm.continuous

theorem ofComps_gInf (g : GA E n) : ofComps (fun v => gInf v g) = GeneralLinearGroup.map (pInf E) g :=
  Units.ext (Matrix.ext fun _ _ => funext fun _ => rfl)

theorem hasCompactSupport_of_section {X Y : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] {F : X → ℂ}
    (p : X → Y) (s : Y → X) (hs : Continuous s) (hsp : ∀ x, s (p x) = x) {K : Set Y} (hK : IsCompact K)
    (hF : ∀ x, F x ≠ 0 → p x ∈ K) : HasCompactSupport F :=
  HasCompactSupport.intro (hK.image hs) fun x hx => by
    by_contra h
    exact hx ⟨p x, hF x h, hsp x⟩

def ofParts (y : ((InfinitePlace E → G a) × (InfinitePlace E → G b)) × Hf E a b) : H E a b :=
  (infGL E a (ofComps y.1.1) * finGL E a y.2.1, infGL E b (ofComps y.1.2) * finGL E b y.2.2)

theorem continuous_ofParts : Continuous (ofParts (E := E) (a := a) (b := b)) :=
  (((_root_.GlobalTheory.GLProj.continuous_proj_incl E a).2.2.1.comp (continuous_ofComps.comp (continuous_fst.comp continuous_fst))).mul
      ((_root_.GlobalTheory.GLProj.continuous_proj_incl E a).2.2.2.comp (continuous_fst.comp continuous_snd))).prodMk
    (((_root_.GlobalTheory.GLProj.continuous_proj_incl E b).2.2.1.comp (continuous_ofComps.comp (continuous_snd.comp continuous_fst))).mul
      ((_root_.GlobalTheory.GLProj.continuous_proj_incl E b).2.2.2.comp (continuous_snd.comp continuous_snd)))

theorem ofParts_parts (g : H E a b) : ofParts ((fun v => gInf v g.1, fun v => gInf v g.2), hFin g) = g := by
  refine Prod.ext ?_ ?_
  · show infGL E a (ofComps fun v => gInf v g.1) * finGL E a (gFin g.1) = g.1
    rw [ofComps_gInf]; exact infGL_mul_finGL g.1
  · show infGL E b (ofComps fun v => gInf v g.2) * finGL E b (gFin g.2) = g.2
    rw [ofComps_gInf]; exact infGL_mul_finGL g.2

theorem entA_adjK (M : Mods E n) (k : Kers M) (i j : IxA M) (g : GA E n) :
    entA (adjK k) i j g = conj (entA k j i g⁻¹) := by
  simp only [entA, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  have e : (gInf v g⁻¹).val = (gInf v g).val⁻¹ := by rw [map_inv]; exact Matrix.coe_units_inv _
  rw [e]
  have := FiniteDimensional.complete ℂ (M v).V
  exact ent_adjoint (M v) _ (i v) (j v)

theorem tens_entry {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [MeasurableSpace (G a)] [MeasurableSpace (G b)]
    {μa : Measure (G a)} {μb : Measure (G b)} {ka : Kers Ma} {kb : Kers Mb} {va vb} {T : ℝ}
    {ψ : Matrix κ κ (Hf E a b → ℂ)} (hA : IsMults μa ka va T) (hB : IsMults μb kb vb T) (hψ : IsFinM ψ)
    (i j : Io Ma Mb κ) : Continuous (tens ka kb ψ i j) ∧ HasCompactSupport (tens ka kb ψ i j) := by
  set_option synthInstance.maxHeartbeats 200000 in
    have cA : ∀ v, Continuous fun y : G a => ent (Ma v) (ka v y.val) (i.1.1 v) (j.1.1 v) := fun v =>
      (mult_ent (hA v) _ _).1
    have cB : ∀ v, Continuous fun y : G b => ent (Mb v) (kb v y.val) (i.1.2 v) (j.1.2 v) := fun v =>
      (mult_ent (hB v) _ _).1
    refine ⟨?_, ?_⟩
    · exact ((continuous_finsetProd _ fun v _ => (cA v).comp ((continuous_gInf a v).comp continuous_fst)).mul
        (continuous_finsetProd _ fun v _ => (cB v).comp ((continuous_gInf b v).comp continuous_snd))).mul
        ((hψ i.2 j.2).1.comp continuous_hFin)
    · refine hasCompactSupport_of_section (fun g : H E a b => ((fun v => gInf v g.1, fun v => gInf v g.2), hFin g))
        ofParts continuous_ofParts ofParts_parts
        (K := (Set.univ.pi (fun v => tsupport fun y : G a => ent (Ma v) (ka v y.val) (i.1.1 v) (j.1.1 v)) ×ˢ
          Set.univ.pi (fun v => tsupport fun y : G b => ent (Mb v) (kb v y.val) (i.1.2 v) (j.1.2 v))) ×ˢ
          tsupport (ψ i.2 j.2))
        (((isCompact_univ_pi fun v => (mult_ent (hA v) _ _).2).prod
          (isCompact_univ_pi fun v => (mult_ent (hB v) _ _).2)).prod (hψ i.2 j.2).2) fun g hg => ?_
      have hg' : entA ka i.1.1 j.1.1 g.1 * entA kb i.1.2 j.1.2 g.2 * ψ i.2 j.2 (hFin g) ≠ 0 := hg
      obtain ⟨⟨h1, h2⟩, h3⟩ := mul_ne_zero_iff.1 hg' |>.imp_left mul_ne_zero_iff.1
      refine ⟨⟨fun v _ => subset_tsupport _ ?_, fun v _ => subset_tsupport _ ?_⟩, subset_tsupport _ h3⟩
      · exact Finset.prod_ne_zero_iff.1 h1 v (Finset.mem_univ v)
      · exact Finset.prod_ne_zero_iff.1 h2 v (Finset.mem_univ v)

theorem tensTest : TensTest := by
  intro E _ _ _ a b _ _ _ _ μa _ μb _ Ma Mb κ _ ka kb va vb T ψ hA hB hψ
  refine ⟨fun i j => tens_entry hA hB hψ i j, ?_⟩
  funext i j y
  show starRingEnd ℂ (tens ka kb ψ j i y⁻¹) = tens (adjK ka) (adjK kb) (adjF ψ) i j y
  simp only [tens, adjF, entA_adjK, map_mul, hFin_inv, Prod.fst_inv, Prod.snd_inv]

end PositivityTheory.Rg.BcB.CG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PCompat
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Measure Topology
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E
open PositivityTheory.RgTw (G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

section Gen

theorem hasCompactSupport_slice {A B : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space B] {F : A × B → ℂ}
    (hF : HasCompactSupport F) (a : A) : HasCompactSupport (fun b => F (a, b)) :=
  HasCompactSupport.intro (hF.isCompact.image continuous_snd) fun b hb =>
    image_eq_zero_of_notMem_tsupport fun h => hb ⟨(a, b), h, rfl⟩

theorem integral_tensor {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] (mX : Measure X) (mY : Measure Y) (mZ : Measure Z) [SigmaFinite mX] [SigmaFinite mY]
    [SigmaFinite mZ] (p : X → ℂ) (q : Y → ℂ) (r : Z → ℂ) :
    ∫ z, p z.1 * q z.2.1 * r z.2.2 ∂(mX.prod (mY.prod mZ)) = (∫ x, p x ∂mX) * (∫ y, q y ∂mY) * ∫ w, r w ∂mZ := by
  calc ∫ z, p z.1 * q z.2.1 * r z.2.2 ∂(mX.prod (mY.prod mZ))
      = ∫ z, p z.1 * (fun w : Y × Z => q w.1 * r w.2) z.2 ∂(mX.prod (mY.prod mZ)) := by simp only [mul_assoc]
    _ = (∫ x, p x ∂mX) * ∫ w, q w.1 * r w.2 ∂(mY.prod mZ) :=
      integral_prod_mul (L := ℂ) (μ := mX) (ν := mY.prod mZ) p (fun w : Y × Z => q w.1 * r w.2)
    _ = _ := by rw [integral_prod_mul (L := ℂ) (μ := mY) (ν := mZ) q r, mul_assoc]

end Gen

section Abstract

variable {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [LocallyCompactSpace Y]
  [SecondCountableTopology Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
variable {Z : Type} [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [LocallyCompactSpace Z]
  [SecondCountableTopology Z] [T2Space Z] [MeasurableSpace Z] [BorelSpace Z]
variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K]

omit [SecondCountableTopology X] in
theorem exists_bump (μ : Measure X) [IsHaarMeasure μ] :
    ∃ f : X → ℂ, Continuous f ∧ HasCompactSupport f ∧ ∫ x, f x ∂μ ≠ 0 := by
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := (1 : X)))
    isClosed_empty (Set.disjoint_empty _)
  refine ⟨fun x => ((f x : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous, hfc.comp_left Complex.ofReal_zero, ?_⟩
  show ∫ x, ((f x : ℝ) : ℂ) ∂μ ≠ 0
  rw [show ∫ x, ((f x : ℝ) : ℂ) ∂μ = ((∫ x, f x ∂μ : ℝ) : ℂ) from integral_ofReal, Complex.ofReal_ne_zero]
  exact (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc (fun x => (hf01 x).1) (x := 1)
    (by simp [hf1 (Set.mem_singleton (1 : X))])).ne'

theorem exists_split (e : X × (Y × Z) ≃ₜ* K) (μ : Measure K) [IsHaarMeasure μ] (mX : Measure X) [IsHaarMeasure mX]
    (mY : Measure Y) [IsHaarMeasure mY] (mZ : Measure Z) [IsHaarMeasure mZ] :
    ∃ c : NNReal, 0 < c ∧ ∀ f : K → ℂ, ∫ g, f g ∂μ = c • ∫ z, f (e z) ∂(mX.prod (mY.prod mZ)) := by
  haveI : IsHaarMeasure (μ.map e.symm) := ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  obtain ⟨c, hc0, h⟩ : ∃ c : NNReal, 0 < c ∧ μ.map e.symm = c • mX.prod (mY.prod mZ) :=
    ⟨_, haarScalarFactor_pos_of_isHaarMeasure _ _, isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨c, hc0, fun f => ?_⟩
  have he : ∫ z, f (e z) ∂(μ.map e.symm) = ∫ g, f g ∂μ := by
    have := integral_map_equiv (μ := μ) (e.toHomeomorph.toMeasurableEquiv.symm) (fun z => f (e z))
    refine this.trans ?_
    congr 1
    funext x
    exact congrArg f (e.apply_symm_apply x)
  rw [← he, h, integral_smul_nnreal_measure]

theorem integral_iter (mX : Measure X) [IsHaarMeasure mX] (mY : Measure Y) [IsHaarMeasure mY] (mZ : Measure Z)
    [IsHaarMeasure mZ] (f : X × (Y × Z) → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ z, f z ∂(mX.prod (mY.prod mZ)) = ∫ x, ∫ y, ∫ w, f (x, (y, w)) ∂mZ ∂mY ∂mX := by
  rw [integral_prod _ (hf.integrable_of_hasCompactSupport hfc)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact integral_prod _ ((hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (hasCompactSupport_slice hfc x))

end Abstract

section Inst

theorem lc_G (n : ℕ) : LocallyCompactSpace (G n) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem sc_G (n : ℕ) : SecondCountableTopology (G n) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

variable (E : Type) [Field E] [NumberField E]

theorem lc_GLf (n : ℕ) : LocallyCompactSpace (GL (Fin n) (Af E)) :=
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Af E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Af E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Af E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem sc_GLf (n : ℕ) : SecondCountableTopology (GL (Fin n) (Af E)) :=
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Af E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

theorem t2_GL_finite_adeles (n : ℕ) : T2Space (GL (Fin n) (Af E)) :=
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  Units.isEmbedding_embedProduct.t2Space

end Inst

attribute [local instance] lc_G sc_G lc_GLf sc_GLf t2_GL_finite_adeles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem borelSpaceH : BorelSpace (H E a b) := ⟨rfl⟩

attribute [local instance] borelSpaceH

theorem haar_of_dom (D : Dom E a b) : IsHaarMeasure D.μ :=
  haveI := D.haar.2.2.2
  { toIsFiniteMeasureOnCompacts := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
    toIsMulLeftInvariant := D.haar.1
    toIsOpenPosMeasure := D.haar.2.2.1 }

def tensH (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ) (g : H E a b) : ℂ :=
  (∏ v, fa v (gInf v g.1)) * (∏ v, fb v (gInf v g.2)) * ψ (hFin g)

theorem tensH_splitH (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ)
    (z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b)) :
    tensH fa fb ψ (splitH a b z) = (∏ v, fa v (z.1 v)) * (∏ v, fb v (z.2.1 v)) * ψ z.2.2 := by
  simp only [tensH, gInf_splitH₁, gInf_splitH₂, hFin_splitH]

theorem integral_tensH_splitH [MeasurableSpace (G a)] [MeasurableSpace (G b)] [MeasurableSpace (Hf E a b)]
    (μa : Measure (G a)) [SigmaFinite μa] (μb : Measure (G b)) [SigmaFinite μb] (ν : Measure (Hf E a b)) [SigmaFinite ν]
    (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ) :
    ∫ z, tensH fa fb ψ (splitH a b z) ∂((Measure.pi fun _ : InfinitePlace E => μa).prod
      ((Measure.pi fun _ : InfinitePlace E => μb).prod ν)) =
      (∏ v, ∫ y, fa v y ∂μa) * (∏ v, ∫ y, fb v y ∂μb) * ∫ h, ψ h ∂ν := by
  simp_rw [tensH_splitH]
  rw [integral_tensor _ _ _ (fun y : InfinitePlace E → G a => ∏ v, fa v (y v))
    (fun y : InfinitePlace E → G b => ∏ v, fb v (y v)) ψ]
  beta_reduce
  rw [integral_fintype_prod_eq_prod, integral_fintype_prod_eq_prod]

theorem compatFub : CompatFub := by
  intro E _ _ _ a b D _ _ _ _ _ _ μa _ μb _ ν _ hC F hF hFc
  haveI := haar_of_dom D
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μa) := pi.isHaarMeasure _
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μb) := pi.isHaarMeasure _
  obtain ⟨c, hc0, hc⟩ := exists_split (splitH a b) D.μ (Measure.pi fun _ : InfinitePlace E => μa)
    (Measure.pi fun _ : InfinitePlace E => μb) ν
  obtain ⟨fa, hfa, hfac, hfa0⟩ := exists_bump μa
  obtain ⟨fb, hfb, hfbc, hfb0⟩ := exists_bump μb
  obtain ⟨ψ, hψ, hψc, hψ0⟩ := exists_bump ν
  have h1 := hC (fun _ => fa) (fun _ => fb) ψ (fun _ => ⟨hfa, hfac⟩) (fun _ => ⟨hfb, hfbc⟩) hψ hψc
  change ∫ g, tensH (fun _ => fa) (fun _ => fb) ψ g ∂D.μ = _ at h1
  rw [hc, integral_tensH_splitH] at h1
  have hc1 : c = 1 := by
    have hne : (∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) * (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ h, ψ h ∂ν ≠ 0 := by
      simp [hfa0, hfb0, hψ0]
    rw [NNReal.smul_def, Complex.real_smul] at h1
    have h2 : ((c : ℝ) : ℂ) = 1 := mul_right_cancel₀ hne (by rw [one_mul]; exact h1)
    exact_mod_cast h2
  rw [hc F, hc1, one_smul]
  exact integral_iter _ _ _ (fun z => F (splitH a b z)) (hF.comp (splitH a b).continuous)
    (hFc.comp_homeomorph (splitH a b).toHomeomorph)

theorem compatEx : CompatEx := by
  intro E _ _ _ a b D _ _ _ _ _ _ μa _ μb _
  haveI := haar_of_dom D
  haveI : D.μ.IsMulRightInvariant := D.haar.2.1
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μa) := pi.isHaarMeasure _
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μb) := pi.isHaarMeasure _
  set ν₀ : Measure (Hf E a b) := Measure.haar
  obtain ⟨c, hc0, hc⟩ := exists_split (splitH a b) D.μ (Measure.pi fun _ : InfinitePlace E => μa)
    (Measure.pi fun _ : InfinitePlace E => μb) ν₀
  obtain ⟨fa, hfa, hfac, hfa0⟩ := exists_bump μa
  obtain ⟨fb, hfb, hfbc, hfb0⟩ := exists_bump μb
  have hR : ∀ h : Hf E a b, ν₀.map (· * h) = ν₀ := by
    intro h
    obtain ⟨k, hk⟩ : ∃ k : NNReal, ν₀.map (· * h) = k • ν₀ := ⟨_, isMulLeftInvariant_eq_smul _ _⟩
    obtain ⟨ψ, hψ, hψc, hψ0⟩ := exists_bump ν₀
    have h1 := integral_mul_right_eq_self (μ := D.μ) (tensH (fun _ => fa) (fun _ => fb) ψ) (splitH a b (1, (1, h)))
    rw [hc, hc] at h1
    have e1 : ∀ z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b),
        tensH (fun _ => fa) (fun _ => fb) ψ (splitH a b z * splitH a b (1, (1, h))) =
          (∏ v, fa (z.1 v)) * (∏ v, fb (z.2.1 v)) * ψ (z.2.2 * h) := by
      intro z
      rw [← map_mul, tensH_splitH]
      simp
    simp_rw [e1] at h1
    rw [integral_tensor _ _ _ (fun y : InfinitePlace E → G a => ∏ v, fa (y v))
      (fun y : InfinitePlace E → G b => ∏ v, fb (y v)) (fun w : Hf E a b => ψ (w * h)),
      integral_tensH_splitH] at h1
    beta_reduce at h1
    rw [integral_fintype_prod_eq_prod, integral_fintype_prod_eq_prod] at h1
    have e2 : ∫ w, ψ (w * h) ∂ν₀ = k • ∫ w, ψ w ∂ν₀ := by
      rw [← integral_smul_nnreal_measure, ← hk, integral_map (measurable_mul_const h).aemeasurable
        hψ.aestronglyMeasurable]
    rw [e2] at h1
    have hne : (∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) * (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ w, ψ w ∂ν₀ ≠ 0 := by
      simp [hfa0, hfb0, hψ0]
    simp only [NNReal.smul_def, Complex.real_smul] at h1
    have hc' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    have h2 : ((k : ℝ) : ℂ) * (((c : ℝ) : ℂ) * ((∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) *
        (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ w, ψ w ∂ν₀)) = 1 * (((c : ℝ) : ℂ) *
        ((∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) * (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ w, ψ w ∂ν₀)) := by
      linear_combination h1
    have h3 : ((k : ℝ) : ℂ) = 1 := mul_right_cancel₀ (mul_ne_zero hc' hne) h2
    have hk1 : k = 1 := by exact_mod_cast h3
    rw [hk, hk1, one_smul]
  haveI : ν₀.IsMulRightInvariant := ⟨hR⟩
  refine ⟨c • ν₀, IsHaarMeasure.nnreal_smul _ hc0.ne', ⟨fun h => by
    rw [Measure.map_smul, hR]
    exact (measurable_mul_const h).aemeasurable⟩, ?_⟩
  intro fa' fb' ψ' hfa' hfb' hψ' hψc'
  change ∫ g, tensH fa' fb' ψ' g ∂D.μ = _
  rw [hc, integral_tensH_splitH, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, Complex.real_smul]
  ring

end PositivityTheory.Rg.BcB.CG

end
end

