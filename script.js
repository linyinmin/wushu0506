let pose;
let poseResults = null;
let video = document.getElementById('video');
let canvas = document.getElementById('output');
let ctx = canvas.getContext('2d');
let startMarkerTime = null;
let endMarkerTime = null;
let currentRotation = 0;
let maxRotation = 0;
let currentRotationCount = 0;
let maxRotationCount = 0;
let previousAngle = null;
let referenceAngle = null;
let currentJumpHeight = 0;
let maxJumpHeight = 0;
let initialFootHeight = null;
let isFirstFrame = true;
let frameCount = 0;
let angleBuffer = [];
const ANGLE_BUFFER_SIZE = 5; // 使用5幀來平滑角度
let isAnalyzing = false;
let isLoopPlayback = false;
let previousAngleDiff = null;

// 新增變數來追蹤起跳和落地狀態
let isJumping = false;
let jumpStartTime = null;
let jumpStartAngle = null;
let jumpEndAngle = null;
let lastGroundTime = null;
let lastGroundAngle = null;

// 新增變數來追蹤腳部高度
let footAboveShoulder = false;
let maxFootHeight = 0;
let shoulderHeight = 0;

// 新增變數來追蹤旋轉和高度
let rotationBuffer = [];
const ROTATION_BUFFER_SIZE = 10;
let heightBuffer = [];
const HEIGHT_BUFFER_SIZE = 5;
let stableShoulderHeight = null;
let stableFootHeight = null;

// 新增變數來追蹤踢腳狀態
let kickState = {
    isInAir: false,
    isKicking: false,
    startTime: null,
    maxHeight: 0,
    minFootHeight: 0,
    maxFootHeight: 0,
    shoulderHeight: 0
};

// 新增變數來追蹤臉部朝向和旋轉狀態
let faceDirectionState = {
    lastFrontFaceTime: 0,
    frontFaceCount: 0,
    isFrontFacing: false,
    rotationStartAngle: null
};

// 新增旋轉信心度追蹤
let rotationConfidence = {
    totalFrames: 0,
    validFrames: 0,
    currentConfidence: 0,
    angleHistory: [],
    HISTORY_SIZE: 20,  // 減少歷史記錄大小
    confidenceThreshold: 0.5,  // 降低信心度閾值
    minValidFrames: 10  // 減少最少需要的有效幀數
};

// 新增旋轉狀態追蹤
let rotationState = {
    startAngle: null,
    currentAngle: null,
    totalRotation: 0,
    rotationDirection: 0,  // 1 順時針, -1 逆時針
    lastQuadrant: null,    // 追蹤上一個象限
    crossCount: 0,         // 穿越次數
    isRotating: false
};

// 新增分析信心度追蹤
let analysisConfidence = {
    rotation: {
        current: 0,
        accumulated: 0,
        count: 0
    },
    kicking: {
        current: 0,
        accumulated: 0,
        count: 0
    },
    getAverageRotation() {
        return this.rotation.count > 0 ? 
            (this.rotation.accumulated / this.rotation.count) : 0;
    },
    getAverageKicking() {
        return this.kicking.count > 0 ? 
            (this.kicking.accumulated / this.kicking.count) : 0;
    },
    getOverallConfidence() {
        return (this.getAverageRotation() * 0.6 + this.getAverageKicking() * 0.4);
    }
};

// 新增穩定性追蹤
let stabilityTracker = {
    frameBuffer: [],
    BUFFER_SIZE: 10,  // 減少緩衝區大小
    rotationHistory: [],
    ROTATION_HISTORY_SIZE: 20,  // 減少歷史記錄大小
    minStableFrames: 3,  // 減少所需穩定幀數
    
    // 添加新的幀數據
    addFrame(landmarks, rotation, isInAir, footAboveShoulder) {
        const frame = {
            landmarks: JSON.parse(JSON.stringify(landmarks)),
            rotation: rotation,
            isInAir: isInAir,
            footAboveShoulder: footAboveShoulder,
            timestamp: Date.now()
        };
        
        this.frameBuffer.push(frame);
        if (this.frameBuffer.length > this.BUFFER_SIZE) {
            this.frameBuffer.shift();
        }
        
        this.rotationHistory.push(rotation);
        if (this.rotationHistory.length > this.ROTATION_HISTORY_SIZE) {
            this.rotationHistory.shift();
        }
    },
    
    // 檢查關鍵點的穩定性
    checkLandmarkStability(landmarkIndex) {
        if (this.frameBuffer.length < this.minStableFrames) return false;
        
        let sumX = 0, sumY = 0, sumZ = 0;
        const recentFrames = this.frameBuffer.slice(-this.minStableFrames);
        
        recentFrames.forEach(frame => {
            const landmark = frame.landmarks[landmarkIndex];
            sumX += landmark.x;
            sumY += landmark.y;
            sumZ += landmark.z || 0;
        });
        
        const avgX = sumX / this.minStableFrames;
        const avgY = sumY / this.minStableFrames;
        const avgZ = sumZ / this.minStableFrames;
        
        let variance = 0;
        recentFrames.forEach(frame => {
            const landmark = frame.landmarks[landmarkIndex];
            variance += Math.pow(landmark.x - avgX, 2) +
                       Math.pow(landmark.y - avgY, 2) +
                       Math.pow(landmark.z || 0 - avgZ, 2);
        });
        
        const stabilityScore = 1 - Math.min(1, variance / (this.minStableFrames * 0.02));  // 增加容許誤差
        return stabilityScore > 0.6;  // 降低穩定性閾值到60%
    },
    
    // 檢查旋轉的穩定性
    checkRotationStability() {
        if (this.rotationHistory.length < this.minStableFrames) return false;
        
        const recentRotations = this.rotationHistory.slice(-this.minStableFrames);
        const avgRotation = recentRotations.reduce((a, b) => a + b, 0) / this.minStableFrames;
        
        // 計算標準差
        const variance = recentRotations.reduce((sum, rot) => 
            sum + Math.pow(rot - avgRotation, 2), 0) / this.minStableFrames;
        const stdDev = Math.sqrt(variance);
        
        return stdDev < 15;  // 增加標準差閾值到15度
    },
    
    // 重置追蹤器
    reset() {
        this.frameBuffer = [];
        this.rotationHistory = [];
    }
};

// 新增動作分析追蹤器
let actionTracker = {
    maxRotation: 0,
    maxJumpHeight: 0,
    hasKickAboveShoulder: false,
    initialFootHeight: null,
    initialShoulderHeight: null,
    rotationConfidence: 0,
    jumpConfidence: 0,
    kickConfidence: 0,
    
    // 更新旋轉角度
    updateRotation(landmarks) {
        if (!landmarks || landmarks.length < 33) return;
        
        const POSE_LANDMARKS = {
            LEFT_SHOULDER: 11,
            RIGHT_SHOULDER: 12,
            LEFT_HIP: 23,
            RIGHT_HIP: 24
        };
        
        // 計算 3D 向量
        const shoulderVector = {
            x: landmarks[POSE_LANDMARKS.RIGHT_SHOULDER].x - landmarks[POSE_LANDMARKS.LEFT_SHOULDER].x,
            y: landmarks[POSE_LANDMARKS.RIGHT_SHOULDER].y - landmarks[POSE_LANDMARKS.LEFT_SHOULDER].y,
            z: landmarks[POSE_LANDMARKS.RIGHT_SHOULDER].z - landmarks[POSE_LANDMARKS.LEFT_SHOULDER].z
        };
        
        const hipVector = {
            x: landmarks[POSE_LANDMARKS.RIGHT_HIP].x - landmarks[POSE_LANDMARKS.LEFT_HIP].x,
            y: landmarks[POSE_LANDMARKS.RIGHT_HIP].y - landmarks[POSE_LANDMARKS.LEFT_HIP].y,
            z: landmarks[POSE_LANDMARKS.RIGHT_HIP].z - landmarks[POSE_LANDMARKS.LEFT_HIP].z
        };
        
        // 計算叉積
        const crossProduct = {
            x: shoulderVector.y * hipVector.z - shoulderVector.z * hipVector.y,
            y: shoulderVector.z * hipVector.x - shoulderVector.x * hipVector.z,
            z: shoulderVector.x * hipVector.y - shoulderVector.y * hipVector.x
        };
        
        // 計算角度
        const currentAngle = Math.atan2(crossProduct.z, crossProduct.x) * (180 / Math.PI);
        
        // 正規化角度到 0-360
        const normalizedAngle = (currentAngle + 360) % 360;
        
        // 更新最大旋轉角度
        if (Math.abs(normalizedAngle) > Math.abs(this.maxRotation)) {
            this.maxRotation = normalizedAngle;
        }
        
        // 計算角加速度
        calculateAngularAcceleration(normalizedAngle, Date.now());
        
        // 更新旋轉信心度
        this.rotationConfidence = Math.min(
            landmarks[POSE_LANDMARKS.LEFT_SHOULDER].visibility,
            landmarks[POSE_LANDMARKS.RIGHT_SHOULDER].visibility,
            landmarks[POSE_LANDMARKS.LEFT_HIP].visibility,
            landmarks[POSE_LANDMARKS.RIGHT_HIP].visibility
        );
    },
    
    // 更新跳躍高度
    updateJumpHeight(landmarks) {
        if (!landmarks || landmarks.length < 33) return;
        
        const POSE_LANDMARKS = {
            LEFT_ANKLE: 27,
            RIGHT_ANKLE: 28
        };
        
        // 檢查可見度
        const leftAnkleVisibility = landmarks[POSE_LANDMARKS.LEFT_ANKLE].visibility;
        const rightAnkleVisibility = landmarks[POSE_LANDMARKS.RIGHT_ANKLE].visibility;
        
        if (leftAnkleVisibility < 0.6 || rightAnkleVisibility < 0.6) return;
        
        // 計算腳踝平均高度
        const currentFootHeight = (landmarks[POSE_LANDMARKS.LEFT_ANKLE].y + 
                                 landmarks[POSE_LANDMARKS.RIGHT_ANKLE].y) / 2;
        
        // 初始化初始高度
        if (this.initialFootHeight === null) {
            this.initialFootHeight = currentFootHeight;
            return;
        }
        
        // 計算跳躍高度（相對於初始高度）
        const jumpHeight = this.initialFootHeight - currentFootHeight;
        
        // 更新最大跳躍高度
        if (jumpHeight > this.maxJumpHeight) {
            this.maxJumpHeight = jumpHeight;
        }
        
        // 更新跳躍信心度
        this.jumpConfidence = (leftAnkleVisibility + rightAnkleVisibility) / 2;
    },
    
    // 檢查踢腳是否過肩
    checkKickAboveShoulder(landmarks) {
        if (!landmarks || landmarks.length < 33) return;
        
        const POSE_LANDMARKS = {
            LEFT_SHOULDER: 11,
            RIGHT_SHOULDER: 12,
            LEFT_ANKLE: 27,
            RIGHT_ANKLE: 28,
            LEFT_WRIST: 15,
            RIGHT_WRIST: 16
        };
        
        // 計算肩膀平均高度和位置
        const shoulderHeight = (landmarks[POSE_LANDMARKS.LEFT_SHOULDER].y + 
                              landmarks[POSE_LANDMARKS.RIGHT_SHOULDER].y) / 2;
        const shoulderZ = (landmarks[POSE_LANDMARKS.LEFT_SHOULDER].z + 
                         landmarks[POSE_LANDMARKS.RIGHT_SHOULDER].z) / 2;
        
        // 計算腳踝平均高度和位置
        const footHeight = (landmarks[POSE_LANDMARKS.LEFT_ANKLE].y + 
                          landmarks[POSE_LANDMARKS.RIGHT_ANKLE].y) / 2;
        const footZ = (landmarks[POSE_LANDMARKS.LEFT_ANKLE].z + 
                     landmarks[POSE_LANDMARKS.RIGHT_ANKLE].z) / 2;
        
        // 計算手腕位置
        const wristX = (landmarks[POSE_LANDMARKS.LEFT_WRIST].x + 
                       landmarks[POSE_LANDMARKS.RIGHT_WRIST].x) / 2;
        const wristY = (landmarks[POSE_LANDMARKS.LEFT_WRIST].y + 
                       landmarks[POSE_LANDMARKS.RIGHT_WRIST].y) / 2;
        
        // 檢查踢腳條件
        const isAboveShoulder = footHeight < shoulderHeight;
        const isInFront = Math.abs(footZ - shoulderZ) < 0.3;  // z 軸差值閾值
        const isNearWrist = Math.abs(footHeight - wristY) < 0.2;  // 與手腕的距離閾值
        
        if (isAboveShoulder && isInFront && isNearWrist) {
            this.hasKickAboveShoulder = true;
        }
        
        // 更新踢腳信心度
        this.kickConfidence = Math.min(
            landmarks[POSE_LANDMARKS.LEFT_ANKLE].visibility,
            landmarks[POSE_LANDMARKS.RIGHT_ANKLE].visibility,
            landmarks[POSE_LANDMARKS.LEFT_SHOULDER].visibility,
            landmarks[POSE_LANDMARKS.RIGHT_SHOULDER].visibility
        );
    },
    
    // 重置追蹤器
    reset() {
        this.maxRotation = 0;
        this.maxJumpHeight = 0;
        this.hasKickAboveShoulder = false;
        this.initialFootHeight = null;
        this.initialShoulderHeight = null;
        this.rotationConfidence = 0;
        this.jumpConfidence = 0;
        this.kickConfidence = 0;
    }
};

// 計算兩點之間的角度
function calculateAngleBetweenPoints(p1, p2) {
    return Math.atan2(p2.x - p1.x, p2.y - p1.y) * (180 / Math.PI);
}

// 標準化角度到 0-360 範圍
function normalizeAngle(angle) {
    angle = angle % 360;
    return angle < 0 ? angle + 360 : angle;
}

// 計算角度差異（考慮跨越360度的情況）
function calculateAngleDifference(angle1, angle2) {
    const diff = normalizeAngle(angle1) - normalizeAngle(angle2);
    if (diff > 180) return diff - 360;
    if (diff < -180) return diff + 360;
    return diff;
}

// 平滑角度值
function smoothAngle(newAngle) {
    angleBuffer.push(newAngle);
    if (angleBuffer.length > ANGLE_BUFFER_SIZE) {
        angleBuffer.shift();
    }
    return angleBuffer.reduce((a, b) => a + b, 0) / angleBuffer.length;
}

// 計算三維空間中兩點之間的距離
function calculate3DDistance(p1, p2) {
    if (!p1 || !p2) return 0;
    const dx = p1.x - p2.x;
    const dy = p1.y - p2.y;
    const dz = (p1.z || 0) - (p2.z || 0);
    return Math.sqrt(dx * dx + dy * dy + dz * dz);
}

// 計算關鍵點的可信度
function calculateLandmarkConfidence(landmarks, indices) {
    if (!landmarks || !indices) return 0;
    let totalConfidence = 0;
    indices.forEach(index => {
        if (landmarks[index]) {
            totalConfidence += landmarks[index].visibility || 0;
        }
    });
    return totalConfidence / indices.length;
}

// 新增骨架顯示相關變數
let showLandmarks = true;
let showConnectors = true;

// 修改 onResults 函數
function onResults(results) {
    if (!results || !results.poseLandmarks) return;
    
    // 儲存最新的結果
    poseResults = results;
    
    // 清除畫布
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    
    // 繪製影像
    ctx.drawImage(results.image, 0, 0, canvas.width, canvas.height);
    
    // 繪製骨架連接線
    if (showConnectors) {
        drawConnectors(ctx, results.poseLandmarks, POSE_CONNECTIONS, 
            {color: '#00FF00', lineWidth: 2});
    }
    
    // 繪製關鍵點
    if (showLandmarks) {
        drawLandmarks(ctx, results.poseLandmarks, 
            {color: '#FF0000', lineWidth: 1, radius: 3});
    }
    
    // 更新視角判斷
    viewMode = estimateViewAngle(results.poseLandmarks);
    
    // 更新動作分析
    if (viewMode !== 'side') {
        actionTracker.updateRotation(results.poseLandmarks);
    }
    actionTracker.updateJumpHeight(results.poseLandmarks);
    actionTracker.checkKickAboveShoulder(results.poseLandmarks);
    
    // 更新顯示
    updateDisplay();
}

// 添加 drawConnectors 函數
function drawConnectors(ctx, landmarks, connections, {color, lineWidth}) {
    ctx.strokeStyle = color;
    ctx.lineWidth = lineWidth;
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    
    for (const [i, j] of connections) {
        const start = landmarks[i];
        const end = landmarks[j];
        
        if (start && end && start.visibility > 0.5 && end.visibility > 0.5) {
            ctx.beginPath();
            ctx.moveTo(start.x * canvas.width, start.y * canvas.height);
            ctx.lineTo(end.x * canvas.width, end.y * canvas.height);
            ctx.stroke();
        }
    }
}

// 添加 drawLandmarks 函數
function drawLandmarks(ctx, landmarks, {color, lineWidth, radius}) {
    ctx.fillStyle = color;
    ctx.strokeStyle = color;
    ctx.lineWidth = lineWidth;
    
    for (const landmark of landmarks) {
        if (landmark.visibility > 0.5) {
            const x = landmark.x * canvas.width;
            const y = landmark.y * canvas.height;
            
            // 繪製圓形
            ctx.beginPath();
            ctx.arc(x, y, radius, 0, 2 * Math.PI);
            ctx.fill();
            
            // 繪製邊框
            ctx.beginPath();
            ctx.arc(x, y, radius, 0, 2 * Math.PI);
            ctx.stroke();
        }
    }
}

// 判斷是否為正面臉部
function isFrontFacing(landmarks) {
    const leftEye = landmarks[2];  // 左眼
    const rightEye = landmarks[5]; // 右眼
    const nose = landmarks[0];     // 鼻子
    const leftEar = landmarks[7];  // 左耳
    const rightEar = landmarks[8]; // 右耳
    
    if (!leftEye || !rightEye || !nose || !leftEar || !rightEar) return false;
    
    // 計算眼睛之間的距離
    const eyeDistance = Math.abs(leftEye.x - rightEye.x);
    // 計算耳朵之間的距離
    const earDistance = Math.abs(leftEar.x - rightEar.x);
    // 計算鼻子到眼睛的距離
    const noseToEyeDistance = Math.abs(nose.y - ((leftEye.y + rightEye.y) / 2));
    
    // 當眼睛距離接近耳朵距離，且鼻子在眼睛下方適當位置時，判定為正面
    const ratio = eyeDistance / earDistance;
    return ratio > 0.7 && noseToEyeDistance > 0;
}

// 計算旋轉信心度
function calculateRotationConfidence(landmarks, rotationAngle) {
    // 增加幀計數
    rotationConfidence.totalFrames++;
    
    // 檢查關鍵點可見度
    const visibilityThreshold = 0.6;  // 降低可見度閾值
    const keyPoints = [
        landmarks[POSE_LANDMARKS.NOSE],
        landmarks[POSE_LANDMARKS.LEFT_EYE],
        landmarks[POSE_LANDMARKS.RIGHT_EYE],
        landmarks[POSE_LANDMARKS.LEFT_SHOULDER],
        landmarks[POSE_LANDMARKS.RIGHT_SHOULDER],
        landmarks[POSE_LANDMARKS.LEFT_HIP],
        landmarks[POSE_LANDMARKS.RIGHT_HIP]
    ];

    // 檢查關鍵點可見度
    const visibilityScore = keyPoints.reduce((sum, point) => 
        sum + (point.visibility || 0), 0) / keyPoints.length;

    // 檢查角度變化的穩定性
    rotationConfidence.angleHistory.push(rotationAngle);
    if (rotationConfidence.angleHistory.length > rotationConfidence.HISTORY_SIZE) {
        rotationConfidence.angleHistory.shift();
    }

    // 計算角度變化的標準差
    const mean = rotationConfidence.angleHistory.reduce((a, b) => a + b, 0) / 
                rotationConfidence.angleHistory.length;
    const variance = rotationConfidence.angleHistory.reduce((a, b) => 
        a + Math.pow(b - mean, 2), 0) / rotationConfidence.angleHistory.length;
    const stdDev = Math.sqrt(variance);

    // 角度變化穩定性分數（標準差越小越好）
    const stabilityScore = Math.max(0, 1 - (stdDev / 60));  // 增加基準值到60度

    // 綜合計算信心度
    const confidence = (visibilityScore * 0.5 + stabilityScore * 0.5);  // 調整權重

    // 更新有效幀計數
    if (confidence > rotationConfidence.confidenceThreshold) {
        rotationConfidence.validFrames++;
    }

    rotationConfidence.currentConfidence = confidence;
    return confidence;
}

// 判斷角度所在象限 (1-4)
function getQuadrant(angle) {
    const normalizedAngle = ((angle % 360) + 360) % 360;
    if (normalizedAngle >= 0 && normalizedAngle < 90) return 1;
    if (normalizedAngle >= 90 && normalizedAngle < 180) return 2;
    if (normalizedAngle >= 180 && normalizedAngle < 270) return 3;
    return 4;
}

// 計算旋轉角度
function calculateRotation(landmarks) {
    if (!landmarks || landmarks.length < 33) return;

    // 定義關鍵點索引
    const POSE_LANDMARKS = {
        NOSE: 0,
        LEFT_EYE_INNER: 1,
        LEFT_EYE: 2,
        LEFT_EYE_OUTER: 3,
        RIGHT_EYE_INNER: 4,
        RIGHT_EYE: 5,
        RIGHT_EYE_OUTER: 6,
        LEFT_EAR: 7,
        RIGHT_EAR: 8,
        LEFT_SHOULDER: 11,
        RIGHT_SHOULDER: 12,
        LEFT_HIP: 23,
        RIGHT_HIP: 24,
        LEFT_KNEE: 25,
        RIGHT_KNEE: 26,
        LEFT_ANKLE: 27,
        RIGHT_ANKLE: 28,
        LEFT_HEEL: 29,
        RIGHT_HEEL: 30,
        LEFT_FOOT_INDEX: 31,
        RIGHT_FOOT_INDEX: 32
    };

    // 檢查關鍵點可信度
    const upperBodyConfidence = calculateLandmarkConfidence(landmarks, 
        [POSE_LANDMARKS.LEFT_SHOULDER, POSE_LANDMARKS.RIGHT_SHOULDER,
         POSE_LANDMARKS.LEFT_HIP, POSE_LANDMARKS.RIGHT_HIP]);
    
    const faceConfidence = calculateLandmarkConfidence(landmarks,
        [POSE_LANDMARKS.NOSE, POSE_LANDMARKS.LEFT_EYE, POSE_LANDMARKS.RIGHT_EYE,
         POSE_LANDMARKS.LEFT_EAR, POSE_LANDMARKS.RIGHT_EAR]);

    // 如果可信度太低，不進行計算
    if (upperBodyConfidence < 0.5 || faceConfidence < 0.5) return;

    // 計算當前旋轉角度
    const shoulderAngle = Math.atan2(
        landmarks[POSE_LANDMARKS.RIGHT_SHOULDER].x - landmarks[POSE_LANDMARKS.LEFT_SHOULDER].x,
        landmarks[POSE_LANDMARKS.RIGHT_SHOULDER].z - landmarks[POSE_LANDMARKS.LEFT_SHOULDER].z
    ) * (180 / Math.PI);

    const hipAngle = Math.atan2(
        landmarks[POSE_LANDMARKS.RIGHT_HIP].x - landmarks[POSE_LANDMARKS.LEFT_HIP].x,
        landmarks[POSE_LANDMARKS.RIGHT_HIP].z - landmarks[POSE_LANDMARKS.LEFT_HIP].z
    ) * (180 / Math.PI);

    // 計算當前角度（標準化到 0-360）
    const currentAngle = ((shoulderAngle * 0.6 + hipAngle * 0.4 + 360) % 360);
    
    // 判斷是否在空中
    const avgAnkleHeight = (landmarks[POSE_LANDMARKS.LEFT_ANKLE].y + 
                           landmarks[POSE_LANDMARKS.RIGHT_ANKLE].y) / 2;
    const isInAir = avgAnkleHeight < (initialFootHeight * 0.95);
    
    // 更新穩定性追蹤器
    stabilityTracker.addFrame(landmarks, currentAngle, isInAir, footAboveShoulder);
    
    // 只在穩定時更新旋轉狀態
    if (stabilityTracker.checkRotationStability()) {
        if (rotationState.startAngle === null) {
            rotationState.startAngle = currentAngle;
            rotationState.currentAngle = currentAngle;
            rotationState.lastQuadrant = getQuadrant(currentAngle);
            return;
        }

        // 取得當前象限
        const currentQuadrant = getQuadrant(currentAngle);
        
        // 檢測是否正在旋轉（需要更穩定的判斷）
        if (!rotationState.isRotating && 
            Math.abs(currentAngle - rotationState.startAngle) > 45 &&
            stabilityTracker.frameBuffer.length >= stabilityTracker.minStableFrames) {
            
            rotationState.isRotating = true;
            rotationState.rotationDirection = currentAngle > rotationState.startAngle ? 1 : -1;
        }

        if (rotationState.isRotating) {
            // 使用穩定的數據來更新旋轉狀態
            updateRotationState(currentAngle, currentQuadrant);
        }
    }
    
    // 更新顯示資訊
    updateDisplay();
}

// 更新旋轉狀態的輔助函數
function updateRotationState(currentAngle, currentQuadrant) {
    // 檢測象限變化
    if (currentQuadrant !== rotationState.lastQuadrant) {
        if (rotationState.rotationDirection === 1 && 
            rotationState.lastQuadrant === 4 && currentQuadrant === 1) {
            rotationState.crossCount++;
        } else if (rotationState.rotationDirection === -1 && 
                  rotationState.lastQuadrant === 1 && currentQuadrant === 4) {
            rotationState.crossCount++;
        }
    }

    // 計算角度差異（使用穩定的數據）
    let angleDiff = currentAngle - rotationState.currentAngle;
    if (Math.abs(angleDiff) > 180) {
        angleDiff = angleDiff > 0 ? angleDiff - 360 : angleDiff + 360;
    }
    
    // 只在角度變化合理時更新
    if (Math.abs(angleDiff) < 45) {  // 增加單幀角度變化限制到45度
        rotationState.totalRotation += angleDiff;
        
        // 更新圈數
        const absoluteRotation = Math.abs(rotationState.totalRotation);
        const fullRotations = Math.floor(absoluteRotation / 360);
        const partialRotation = (absoluteRotation % 360) / 360;
        
        // 更新顯示
        currentRotation = rotationState.totalRotation;
        currentRotationCount = (fullRotations + partialRotation).toFixed(2);
        
        // 更新最大值（只在完整旋轉時更新）
        if (Math.abs(currentRotation) > Math.abs(maxRotation) && 
            stabilityTracker.checkRotationStability()) {
            maxRotation = currentRotation;
            maxRotationCount = currentRotationCount;
        }
    }
    
    // 更新當前角度
    rotationState.currentAngle = currentAngle;
    rotationState.lastQuadrant = currentQuadrant;
}

// 重置分析數據
function resetAnalysis() {
    currentRotation = 0;
    maxRotation = 0;
    currentRotationCount = 0;
    maxRotationCount = 0;
    previousAngle = null;
    referenceAngle = null;
    currentJumpHeight = 0;
    maxJumpHeight = 0;
    initialFootHeight = null;
    isFirstFrame = true;
    frameCount = 0;
    angleBuffer = [];
    previousAngleDiff = null;
    
    // 重置跳躍相關變數
    isJumping = false;
    jumpStartTime = null;
    jumpStartAngle = null;
    jumpEndAngle = null;
    lastGroundTime = null;
    lastGroundAngle = null;
    
    // 重置腳部高度相關變數
    footAboveShoulder = false;
    maxFootHeight = 0;
    shoulderHeight = 0;
    
    // 重置旋轉和高度相關變數
    rotationBuffer = [];
    heightBuffer = [];
    stableShoulderHeight = null;
    stableFootHeight = null;
    
    // 重置踢腳狀態
    kickState = {
        isInAir: false,
        isKicking: false,
        startTime: null,
        maxHeight: 0,
        minFootHeight: 0,
        maxFootHeight: 0,
        shoulderHeight: 0
    };
    
    // 重置臉部朝向狀態
    faceDirectionState = {
        lastFrontFaceTime: 0,
        frontFaceCount: 0,
        isFrontFacing: false,
        rotationStartAngle: null
    };
    
    // 重置旋轉信心度
    rotationConfidence = {
        totalFrames: 0,
        validFrames: 0,
        currentConfidence: 0,
        angleHistory: [],
        HISTORY_SIZE: 20,
        confidenceThreshold: 0.5,
        minValidFrames: 10
    };
    
    // 重置旋轉狀態
    rotationState = {
        startAngle: null,
        currentAngle: null,
        totalRotation: 0,
        rotationDirection: 0,
        lastQuadrant: null,
        crossCount: 0,
        isRotating: false
    };
    
    // 重置信心程度
    analysisConfidence = {
        rotation: {
            current: 0,
            accumulated: 0,
            count: 0
        },
        kicking: {
            current: 0,
            accumulated: 0,
            count: 0
        },
        getAverageRotation() {
            return this.rotation.count > 0 ? 
                (this.rotation.accumulated / this.rotation.count) : 0;
        },
        getAverageKicking() {
            return this.kicking.count > 0 ? 
                (this.kicking.accumulated / this.kicking.count) : 0;
        },
        getOverallConfidence() {
            return (this.getAverageRotation() * 0.6 + this.getAverageKicking() * 0.4);
        }
    };
    
    // 重置穩定性追蹤器
    stabilityTracker.reset();
    
    // 重置動作分析追蹤器
    actionTracker.reset();
    
    // 更新顯示
    updateDisplay();
}

// 新增角加速度轉換函式
function formatAngularAcceleration(acceleration) {
    if (!acceleration || acceleration === 0) {
        return {
            text: "尚未偵測到旋轉加速度",
            level: "",
            circlesPerSecond: 0
        };
    }
    
    // 轉換為每秒圈數
    const circlesPerSecond = Math.abs(acceleration) / 360;
    
    // 判斷星等
    let level = "";
    if (Math.abs(acceleration) < 360) {
        level = "★ 加速緩慢";
    } else if (Math.abs(acceleration) < 720) {
        level = "★★ 中等加速";
    } else if (Math.abs(acceleration) < 1080) {
        level = "★★★ 良好加速";
    } else if (Math.abs(acceleration) < 1440) {
        level = "★★★★ 快速旋轉";
    } else {
        level = "★★★★★ 爆發性旋轉（專業等級）";
    }
    
    return {
        text: `🌪 旋轉爆發力：每秒加速 ${circlesPerSecond.toFixed(1)} 圈`,
        level: level,
        circlesPerSecond: circlesPerSecond
    };
}

// 修改 updateDisplay 函數
function updateDisplay() {
    // 更新視角資訊
    const viewModeInfo = document.getElementById('viewModeInfo');
    if (viewModeInfo) {
        viewModeInfo.textContent = `拍攝視角: ${viewMode || '分析中...'}`;
    }
    
    // 更新旋轉資訊
    const rotationInfo = document.getElementById('rotationInfo');
    if (rotationInfo) {
        if (viewMode === 'side') {
            rotationInfo.textContent = '旋轉分析不可靠（側面拍攝）';
        } else {
            rotationInfo.textContent = `最大旋轉角度: ${Math.abs(actionTracker.maxRotation).toFixed(2)}° (信心度: ${(actionTracker.rotationConfidence * 100).toFixed(1)}%)`;
        }
    }
    
    // 更新跳躍資訊
    const jumpInfo = document.getElementById('jumpInfo');
    if (jumpInfo) {
        jumpInfo.textContent = `最大跳躍高度: ${(actionTracker.maxJumpHeight * 100).toFixed(2)} cm (信心度: ${(actionTracker.jumpConfidence * 100).toFixed(1)}%)`;
    }
    
    // 更新踢腳資訊
    const kickInfo = document.getElementById('kickInfo');
    if (kickInfo) {
        kickInfo.textContent = `踢腳過肩: ${actionTracker.hasKickAboveShoulder ? '是' : '否'} (信心度: ${(actionTracker.kickConfidence * 100).toFixed(1)}%)`;
    }
    
    // 更新角加速度資訊
    const accelerationResult = formatAngularAcceleration(maxAngularAcceleration);
    
    // 更新左側面板的分析結果
    const resultSection = document.querySelector('.result-section');
    if (resultSection) {
        // 更新即時資訊
        document.getElementById('currentRotationAngle').textContent = 
            Math.abs(currentRotation).toFixed(2);
        document.getElementById('currentRotationCount').textContent = 
            currentRotationCount;
        document.getElementById('currentJumpHeight').textContent = 
            currentJumpHeight.toFixed(2);
        
        // 更新最大值統計
        document.getElementById('maxRotationAngle').textContent = 
            Math.abs(actionTracker.maxRotation).toFixed(2);
        document.getElementById('maxRotationCount').textContent = 
            maxRotationCount;
        document.getElementById('maxJumpHeight').textContent = 
            (actionTracker.maxJumpHeight * 100).toFixed(2);
        
        // 新增角加速度資訊
        const accelerationInfo = document.createElement('p');
        accelerationInfo.innerHTML = `${accelerationResult.text}<br>${accelerationResult.level}`;
        
        // 檢查是否已存在角加速度資訊
        const existingAccInfo = resultSection.querySelector('.acceleration-info');
        if (existingAccInfo) {
            existingAccInfo.innerHTML = accelerationInfo.innerHTML;
        } else {
            accelerationInfo.className = 'acceleration-info';
            resultSection.appendChild(accelerationInfo);
        }
    }
}

// 新增視角判斷相關變數
let viewMode = null;
let angularVelocity = 0;
let maxAngularAcceleration = 0;
let lastAngle = null;
let lastTime = null;

// 更新 MediaPipe 初始化設定
async function initializePose() {
    try {
        pose = new Pose({
            locateFile: (file) => {
                return `https://cdn.jsdelivr.net/npm/@mediapipe/pose/${file}`;
            }
        });

        // 設置模型配置為 heavy 模式
        pose.setOptions({
            modelComplexity: 2,  // heavy 模式
            smoothLandmarks: true,
            enableSegmentation: true,
            smoothSegmentation: true,
            minDetectionConfidence: 0.5,
            minTrackingConfidence: 0.5,
            useZ: true  // 啟用 3D 偵測
        });

        pose.onResults(onResults);
    } catch (error) {
        console.error('初始化 MediaPipe Pose 時發生錯誤:', error);
    }
}

// 新增視角判斷函數
function estimateViewAngle(landmarks) {
    if (!landmarks || landmarks.length < 33) return null;
    
    const POSE_LANDMARKS = {
        LEFT_SHOULDER: 11,
        RIGHT_SHOULDER: 12,
        LEFT_HIP: 23,
        RIGHT_HIP: 24
    };
    
    // 計算肩膀和髖部的 z 軸差值
    const shoulderZDiff = Math.abs(
        landmarks[POSE_LANDMARKS.RIGHT_SHOULDER].z - 
        landmarks[POSE_LANDMARKS.LEFT_SHOULDER].z
    );
    
    const hipZDiff = Math.abs(
        landmarks[POSE_LANDMARKS.RIGHT_HIP].z - 
        landmarks[POSE_LANDMARKS.LEFT_HIP].z
    );
    
    // 計算肩膀和髖部的 x 軸差值
    const shoulderXDiff = Math.abs(
        landmarks[POSE_LANDMARKS.RIGHT_SHOULDER].x - 
        landmarks[POSE_LANDMARKS.LEFT_SHOULDER].x
    );
    
    const hipXDiff = Math.abs(
        landmarks[POSE_LANDMARKS.RIGHT_HIP].x - 
        landmarks[POSE_LANDMARKS.LEFT_HIP].x
    );
    
    // 計算平均差值
    const avgZDiff = (shoulderZDiff + hipZDiff) / 2;
    const avgXDiff = (shoulderXDiff + hipXDiff) / 2;
    
    // 判斷視角
    if (avgZDiff < 0.1) {  // z 差值接近 0
        return 'side';
    } else if (avgXDiff < 0.1) {  // x 差值接近 0
        return 'front';
    } else {
        return 'angled';
    }
}

// 新增角加速度計算函數
function calculateAngularAcceleration(currentAngle, currentTime) {
    if (lastAngle === null || lastTime === null) {
        lastAngle = currentAngle;
        lastTime = currentTime;
        return 0;
    }
    
    // 計算角速度
    const deltaTime = (currentTime - lastTime) / 1000;  // 轉換為秒
    const deltaAngle = currentAngle - lastAngle;
    const currentAngularVelocity = deltaAngle / deltaTime;
    
    // 計算角加速度
    const angularAcceleration = (currentAngularVelocity - angularVelocity) / deltaTime;
    
    // 更新最大值
    if (Math.abs(angularAcceleration) > Math.abs(maxAngularAcceleration)) {
        maxAngularAcceleration = angularAcceleration;
    }
    
    // 更新狀態
    angularVelocity = currentAngularVelocity;
    lastAngle = currentAngle;
    lastTime = currentTime;
    
    return angularAcceleration;
}

// 影片資訊
const videoInfo = {
    'V1.mp4': { date: '2025-04-30 14:30:00' },
    'V2.mp4': { date: '2025-04-30 14:45:00' },
    'V3.mp4': { date: '2025-04-30 15:00:00' },
    'V4.mp4': { date: '2025-04-30 15:15:00' },
    'V5.mp4': { date: '2025-04-30 15:30:00' },
    'V6.mp4': { date: '2025-04-30 15:45:00' },
    'V7.mp4': { date: '2025-04-30 16:00:00' }
};

// 更新影片資訊顯示
function updateVideoInfo(filename) {
    const fileNameElement = document.getElementById('videoFileName');
    const dateTimeElement = document.getElementById('videoDateTime');
    
    fileNameElement.textContent = filename;
    if (videoInfo[filename]) {
        dateTimeElement.textContent = videoInfo[filename].date;
    } else {
        dateTimeElement.textContent = '未知';
    }
}

// 影片列表
const videoFiles = [
    'https://raw.githubusercontent.com/linyinmin/wushu0506/main/video/V1.mp4',
    'https://raw.githubusercontent.com/linyinmin/wushu0506/main/video/V2.mp4',
    'https://raw.githubusercontent.com/linyinmin/wushu0506/main/video/V3.mp4',
    'https://raw.githubusercontent.com/linyinmin/wushu0506/main/video/V4.mp4',
    'https://raw.githubusercontent.com/linyinmin/wushu0506/main/video/V5.mp4',
    'https://raw.githubusercontent.com/linyinmin/wushu0506/main/video/V6.mp4',
    'https://raw.githubusercontent.com/linyinmin/wushu0506/main/video/V7.mp4'
];

// 修改影片載入函數
async function loadVideo(videoPath) {
    try {
        console.log('開始載入影片:', videoPath);
        const video = document.getElementById('video');
        
        // 重置分析狀態
        resetAnalysis();
        
        // 設置跨域屬性
        video.crossOrigin = 'anonymous';
        
        // 使用 fetch 載入影片
        const response = await fetch(videoPath);
        if (!response.ok) {
            throw new Error(`HTTP error! status: ${response.status}`);
        }
        
        // 創建 blob URL
        const blob = await response.blob();
        const blobUrl = URL.createObjectURL(blob);
        
        // 設置影片來源
        video.src = blobUrl;
        
        // 更新影片資訊
        updateVideoInfo(videoPath.split('/').pop());
        
        // 等待影片載入完成
        await new Promise((resolve, reject) => {
            video.onloadedmetadata = () => {
                console.log('影片元數據已載入');
                
                const container = document.querySelector('.canvas-container');
                const containerWidth = container.clientWidth;
                const containerHeight = container.clientHeight;
                
                canvas.width = containerWidth;
                canvas.height = containerHeight;
                
                video.style.width = '100%';
                video.style.height = '100%';
                canvas.style.width = '100%';
                canvas.style.height = '100%';
                
                // 初始化 MediaPipe
                initializePose();
                
                // 設置影片事件監聽器
                video.addEventListener('seeked', () => {
                    if (poseResults) {
                        onResults(poseResults);
                    }
                });
                
                video.addEventListener('timeupdate', () => {
                    if (poseResults) {
                        onResults(poseResults);
                    }
                });
                
                resolve();
            };
            
            video.onerror = (error) => {
                console.error('影片載入錯誤:', error);
                showError('影片載入失敗，請檢查檔案路徑或網路連線');
                reject(error);
            };
        });
        
        // 開始分析第一幀
        video.pause();
        video.currentTime = 0;
        await pose.send({image: video});
        
    } catch (error) {
        console.error('載入影片時發生錯誤:', error);
        showError(`載入影片時發生錯誤: ${error.message}`);
    }
}

// 修改檔案上傳處理
document.getElementById('videoInput').addEventListener('change', async (event) => {
    const file = event.target.files[0];
    if (file) {
        resetAnalysis();
        const videoUrl = URL.createObjectURL(file);
        video.src = videoUrl;
        video.load();
        
        // 更新影片資訊
        updateVideoInfo(file.name);
        
        video.onloadedmetadata = () => {
            // 設置畫布大小與影片相同
            const container = document.querySelector('.canvas-container');
            const containerWidth = container.clientWidth;
            const containerHeight = container.clientHeight;
            
            canvas.width = containerWidth;
            canvas.height = containerHeight;
            
            // 設置影片和畫布的顯示大小
            video.style.width = '100%';
            video.style.height = '100%';
            canvas.style.width = '100%';
            canvas.style.height = '100%';
            
            initializePose();
        };
    }
});

// 處理影片播放
video.addEventListener('play', () => {
    resetAnalysis();
    let lastFrameTime = 0;
    const frameInterval = 1000 / 60; // 提高到60fps
    
    const detectFrame = async () => {
        if (video.paused || video.ended) return;
        
        const currentTime = performance.now();
        if (currentTime - lastFrameTime >= frameInterval) {
            await pose.send({image: video});
            lastFrameTime = currentTime;
        }
        requestAnimationFrame(detectFrame);
    };
    detectFrame();
});

// 新增幀控制相關變數
let frameInterval = null;
let frameStepSize = 0.04; // 每幀的時間間隔（秒）
let isFrameStepping = false;

// 修改幀控制函數
function initializeFrameControls() {
    const prevFrameBtn = document.getElementById('prevFrameBtn');
    const nextFrameBtn = document.getElementById('nextFrameBtn');
    
    // 前一幀按鈕事件
    prevFrameBtn.addEventListener('click', function() {
        video.pause();
        video.currentTime = Math.max(0, video.currentTime - frameStepSize);
        updateTimeDisplay();
        // 立即更新骨架顯示
        if (poseResults) {
            onResults(poseResults);
        }
    });
    
    // 下一幀按鈕事件
    nextFrameBtn.addEventListener('click', function() {
        video.pause();
        video.currentTime = Math.min(video.duration, video.currentTime + frameStepSize);
        updateTimeDisplay();
        // 立即更新骨架顯示
        if (poseResults) {
            onResults(poseResults);
        }
    });
    
    // 觸控設備支援
    prevFrameBtn.addEventListener('touchstart', function(e) {
        e.preventDefault();
        video.pause();
        video.currentTime = Math.max(0, video.currentTime - frameStepSize);
        updateTimeDisplay();
        // 立即更新骨架顯示
        if (poseResults) {
            onResults(poseResults);
        }
    });
    
    nextFrameBtn.addEventListener('touchstart', function(e) {
        e.preventDefault();
        video.pause();
        video.currentTime = Math.min(video.duration, video.currentTime + frameStepSize);
        updateTimeDisplay();
        // 立即更新骨架顯示
        if (poseResults) {
            onResults(poseResults);
        }
    });
}

// 修改時間滑桿控制
function initializePlaybackControls() {
    const timeSlider = document.getElementById('timeSlider');
    const currentTimeDisplay = document.getElementById('currentTime');
    const durationDisplay = document.getElementById('duration');
    const playbackSpeedSelect = document.getElementById('playbackSpeed');
    
    // 更新時間滑桿
    video.addEventListener('loadedmetadata', () => {
        const maxValue = Math.floor(video.duration * 1000);
        timeSlider.max = maxValue;
        timeSlider.value = 0;
        timeSlider.step = 1;
        durationDisplay.textContent = formatTime(video.duration);
    });
    
    // 時間滑桿控制
    timeSlider.addEventListener('input', () => {
        const time = parseFloat(timeSlider.value) / 1000;
        video.currentTime = time;
        updateTimeDisplay();
        
        // 立即更新骨架顯示
        if (poseResults) {
            onResults(poseResults);
        }
    });
    
    // 影片播放時更新滑桿和時間顯示
    video.addEventListener('timeupdate', () => {
        if (!timeSlider.dragging) {
            timeSlider.value = Math.floor(video.currentTime * 1000);
            updateTimeDisplay();
            
            // 立即更新骨架顯示
            if (poseResults) {
                onResults(poseResults);
            }
        }
    });
    
    // 添加滑桿拖動結束事件
    timeSlider.addEventListener('change', () => {
        // 確保在滑桿拖動結束時更新骨架顯示
        if (poseResults) {
            onResults(poseResults);
        }
    });
    
    // 播放速度控制
    playbackSpeedSelect.addEventListener('change', () => {
        const speed = parseFloat(playbackSpeedSelect.value);
        video.playbackRate = speed;
    });
    
    // 防止拖動時持續更新
    timeSlider.addEventListener('mousedown', () => {
        timeSlider.dragging = true;
    });
    
    timeSlider.addEventListener('mouseup', () => {
        timeSlider.dragging = false;
        // 確保在釋放滑鼠時更新骨架顯示
        if (poseResults) {
            onResults(poseResults);
        }
    });
    
    // 添加觸控支援
    timeSlider.addEventListener('touchstart', () => {
        timeSlider.dragging = true;
    });
    
    timeSlider.addEventListener('touchend', () => {
        timeSlider.dragging = false;
        // 確保在釋放觸控時更新骨架顯示
        if (poseResults) {
            onResults(poseResults);
        }
    });
    
    // 修改鍵盤控制
    document.addEventListener('keydown', (e) => {
        // 防止按鍵預設行為
        if (['ArrowDown', 'ArrowLeft', 'ArrowRight'].includes(e.code)) {
            e.preventDefault();
        }
        
        switch(e.code) {
            case 'ArrowDown': // 向下鍵：播放/暫停
                if (video.paused) {
                    video.play();
                } else {
                    video.pause();
                }
                break;
            
            case 'ArrowLeft': // 左方向鍵：上一幀
                video.pause();
                video.currentTime = Math.max(0, video.currentTime - frameStepSize);
                updateTimeDisplay();
                // 更新骨架顯示
                if (poseResults) {
                    onResults(poseResults);
                }
                break;
            
            case 'ArrowRight': // 右方向鍵：下一幀
                video.pause();
                video.currentTime = Math.min(video.duration, video.currentTime + frameStepSize);
                updateTimeDisplay();
                // 更新骨架顯示
                if (poseResults) {
                    onResults(poseResults);
                }
                break;
        }
    });
}

// 初始化界面
document.addEventListener('DOMContentLoaded', () => {
    try {
        console.log('DOM 已載入，開始初始化界面');
        
        let currentVideoIndex = 0;
        
        // 添加重置按鈕
        const resetButton = document.getElementById('resetButton');
        resetButton.onclick = () => {
            resetAnalysis();
            resetCanvasTransform();
        };
        
        // 初始化播放控制
        initializePlaybackControls();
        
        // 初始化幀控制
        initializeFrameControls();
        
        // 初始化影片控制
        const prevButton = document.getElementById('prevButton');
        const nextButton = document.getElementById('nextButton');
        
        prevButton.onclick = () => {
            currentVideoIndex = (currentVideoIndex - 1 + videoFiles.length) % videoFiles.length;
            loadVideo(videoFiles[currentVideoIndex]);
        };
        
        nextButton.onclick = () => {
            currentVideoIndex = (currentVideoIndex + 1) % videoFiles.length;
            loadVideo(videoFiles[currentVideoIndex]);
        };
        
        // 設置標記按鈕事件
        const startMarkerBtn = document.getElementById('startMarkerBtn');
        const endMarkerBtn = document.getElementById('endMarkerBtn');
        const clearMarkersBtn = document.getElementById('clearMarkersBtn');
        const startAnalysisBtn = document.getElementById('startAnalysisBtn');
        
        if (startMarkerBtn) {
            startMarkerBtn.onclick = () => {
                if (video) {
                    startMarkerTime = video.currentTime;
                    updateMarkerControls();
                    updateTimeDisplay();
                }
            };
        }
        
        if (endMarkerBtn) {
            endMarkerBtn.onclick = () => {
                if (video) {
                    endMarkerTime = video.currentTime;
                    updateMarkerControls();
                    updateTimeDisplay();
                }
            };
        }
        
        if (clearMarkersBtn) {
            clearMarkersBtn.onclick = () => {
                startMarkerTime = null;
                endMarkerTime = null;
                isLoopPlayback = false;
                isAnalyzing = false;
                updateMarkerControls();
                updateTimeDisplay();
                resetAnalysis();
            };
        }
        
        if (startAnalysisBtn) {
            startAnalysisBtn.onclick = () => {
                if (startMarkerTime !== null && endMarkerTime !== null) {
                    isAnalyzing = true;
                    isLoopPlayback = true;
                    video.currentTime = startMarkerTime;
                    video.play();
                    startAnalysisBtn.disabled = true;
                    startAnalysisBtn.textContent = '分析中...';
                }
            };
        }
        
        // 載入第一個影片
        loadVideo(videoFiles[0]);
        
        // 初始化縮放功能
        initializeCanvasZoom();
        
        console.log('界面初始化完成');
        
    } catch (error) {
        console.error('初始化界面時發生錯誤:', error);
        showError(`初始化界面時發生錯誤: ${error.message}`);
    }
});

// 定義骨架連接點
const POSE_CONNECTIONS = [
    [11, 12], // 左肩到右肩
    [11, 13], // 左肩到左手肘
    [13, 15], // 左手肘到左手腕
    [12, 14], // 右肩到右手肘
    [14, 16], // 右手肘到右手腕
    [11, 23], // 左肩到左髖
    [12, 24], // 右肩到右髖
    [23, 24], // 左髖到右髖
    [23, 25], // 左髖到左膝
    [25, 27], // 左膝到左腳踝
    [24, 26], // 右髖到右膝
    [26, 28]  // 右膝到右腳踝
];

// 錯誤處理函數
function showError(message) {
    const errorDiv = document.getElementById('error-message');
    errorDiv.textContent = message;
    errorDiv.style.display = 'block';
    console.error(message);
}

// 更新時間顯示
function updateTimeDisplay() {
    if (video) {
        const currentTime = video.currentTime;
        const duration = video.duration;
        
        // 更新當前時間顯示
        const currentTimeDisplay = document.getElementById('currentTime');
        if (currentTimeDisplay) {
            currentTimeDisplay.textContent = formatTime(currentTime);
        }
        
        // 更新總時長顯示
        const durationDisplay = document.getElementById('duration');
        if (durationDisplay) {
            durationDisplay.textContent = formatTime(duration);
        }
        
        // 更新標記資訊
        const markerInfo = document.getElementById('markerInfo');
        if (markerInfo) {
            let markerText = '';
            if (startMarkerTime !== null) {
                markerText += `起始點: ${formatTime(startMarkerTime)}`;
            }
            if (endMarkerTime !== null) {
                markerText += markerText ? ` | 結束點: ${formatTime(endMarkerTime)}` : `結束點: ${formatTime(endMarkerTime)}`;
            }
            if (!markerText) {
                markerText = '未設置標記點';
            }
            markerInfo.textContent = markerText;
        }
        
        // 檢查是否需要循環播放
        if (isLoopPlayback && endMarkerTime !== null && currentTime >= endMarkerTime) {
            video.currentTime = startMarkerTime || 0;
        }
    }
}

function calculateRotationAngle(pose) {
    if (!pose || !pose.keypoints) return 0;
    
    // 獲取腳尖點（31和32）和肩膀點（11和12）
    const leftToe = pose.keypoints.find(k => k.part === 'left_toe');
    const rightToe = pose.keypoints.find(k => k.part === 'right_toe');
    const leftShoulder = pose.keypoints.find(k => k.part === 'left_shoulder');
    const rightShoulder = pose.keypoints.find(k => k.part === 'right_shoulder');
    
    if (!leftToe || !rightToe || !leftShoulder || !rightShoulder || 
        leftToe.score < 0.5 || rightToe.score < 0.5 || 
        leftShoulder.score < 0.5 || rightShoulder.score < 0.5) return 0;
    
    // 計算腳尖連線的向量
    const toeVector = {
        x: rightToe.position.x - leftToe.position.x,
        y: rightToe.position.y - leftToe.position.y
    };
    
    // 計算肩膀連線的向量
    const shoulderVector = {
        x: rightShoulder.position.x - leftShoulder.position.x,
        y: rightShoulder.position.y - leftShoulder.position.y
    };
    
    // 計算兩個向量的平均角度
    const toeAngle = Math.atan2(toeVector.y, toeVector.x);
    const shoulderAngle = Math.atan2(shoulderVector.y, shoulderVector.x);
    
    // 計算平均角度（考慮角度跨越 180/-180 的情況）
    let avgAngle = (toeAngle + shoulderAngle) / 2;
    
    // 轉換為角度（0-360度）
    let angleDeg = (avgAngle * 180 / Math.PI + 360) % 360;
    
    // 將角度轉換為 -180 到 180 的範圍
    if (angleDeg > 180) {
        angleDeg -= 360;
    }
    
    return angleDeg;
}

function calculateRotationCount(pose, prevAngle, totalRotations) {
    if (!pose || !pose.keypoints) return totalRotations;
    
    const currentAngle = calculateRotationAngle(pose);
    
    // 計算角度變化
    let angleDiff = currentAngle - prevAngle;
    
    // 處理角度跨越 180/-180 的情況
    if (angleDiff > 180) {
        angleDiff -= 360;
    } else if (angleDiff < -180) {
        angleDiff += 360;
    }
    
    // 累計旋轉圈數（每360度為一圈）
    const newRotations = totalRotations + (angleDiff / 360);
    
    return newRotations;
}

// 更新標記點控制
function updateMarkerControls() {
    const startAnalysisBtn = document.getElementById('startAnalysisBtn');
    const startMarkerBtn = document.getElementById('startMarkerBtn');
    const endMarkerBtn = document.getElementById('endMarkerBtn');
    
    // 更新開始分析按鈕狀態
    if (startMarkerTime !== null && endMarkerTime !== null) {
        startAnalysisBtn.disabled = false;
    } else {
        startAnalysisBtn.disabled = true;
    }
    
    // 更新標記按鈕狀態
    if (startMarkerTime !== null) {
        startMarkerBtn.classList.add('active');
    } else {
        startMarkerBtn.classList.remove('active');
    }
    
    if (endMarkerTime !== null) {
        endMarkerBtn.classList.add('active');
    } else {
        endMarkerBtn.classList.remove('active');
    }
    
    // 更新時間顯示
    updateTimeDisplay();
}

// 添加骨架縮放相關變數
let canvasScale = 1;
const MIN_SCALE = 0.5;
const MAX_SCALE = 2;
let isDragging = false;
let lastX = 0;
let lastY = 0;
let translateX = 0;
let translateY = 0;
let isFullscreen = false;
let originalContainerStyle = null;

// 修改 initializeCanvasZoom 函數
function initializeCanvasZoom() {
    const canvasContainer = document.querySelector('.canvas-container');
    
    // 添加骨架顯示控制按鈕
    const controlsDiv = document.createElement('div');
    controlsDiv.style.position = 'absolute';
    controlsDiv.style.top = '10px';
    controlsDiv.style.left = '10px';
    controlsDiv.style.zIndex = '1000';
    controlsDiv.style.display = 'flex';
    controlsDiv.style.gap = '10px';
    
    // 關鍵點開關按鈕
    const landmarksBtn = document.createElement('button');
    landmarksBtn.className = 'tiss-btn tiss-btn-outline';
    landmarksBtn.textContent = '關鍵點';
    landmarksBtn.style.backgroundColor = showLandmarks ? 'var(--accent-color)' : 'var(--dark-panel)';
    landmarksBtn.style.color = showLandmarks ? '#ffffff' : 'var(--dark-text)';
    landmarksBtn.style.border = '1px solid var(--dark-border)';
    landmarksBtn.style.padding = '6px 12px';
    landmarksBtn.style.fontSize = '14px';
    landmarksBtn.style.borderRadius = '4px';
    landmarksBtn.style.cursor = 'pointer';
    landmarksBtn.style.transition = 'all 0.3s ease';
    
    // 連接線開關按鈕
    const connectorsBtn = document.createElement('button');
    connectorsBtn.className = 'tiss-btn tiss-btn-outline';
    connectorsBtn.textContent = '連接線';
    connectorsBtn.style.backgroundColor = showConnectors ? 'var(--accent-color)' : 'var(--dark-panel)';
    connectorsBtn.style.color = showConnectors ? '#ffffff' : 'var(--dark-text)';
    connectorsBtn.style.border = '1px solid var(--dark-border)';
    connectorsBtn.style.padding = '6px 12px';
    connectorsBtn.style.fontSize = '14px';
    connectorsBtn.style.borderRadius = '4px';
    connectorsBtn.style.cursor = 'pointer';
    connectorsBtn.style.transition = 'all 0.3s ease';
    
    // 全螢幕按鈕
    const fullscreenBtn = document.createElement('button');
    fullscreenBtn.className = 'tiss-btn tiss-btn-outline';
    fullscreenBtn.textContent = '全螢幕';
    fullscreenBtn.style.backgroundColor = 'var(--dark-panel)';
    fullscreenBtn.style.color = 'var(--dark-text)';
    fullscreenBtn.style.border = '1px solid var(--dark-border)';
    fullscreenBtn.style.padding = '6px 12px';
    fullscreenBtn.style.fontSize = '14px';
    fullscreenBtn.style.borderRadius = '4px';
    fullscreenBtn.style.cursor = 'pointer';
    fullscreenBtn.style.transition = 'all 0.3s ease';
    
    fullscreenBtn.onclick = () => {
        const canvasContainer = document.querySelector('.canvas-container');
        // 確保移除可能存在的舊退出按鈕
        const existingExitButton = document.querySelector('.exit-fullscreen-btn');
        if (existingExitButton) {
            document.body.removeChild(existingExitButton);
        }
        // 重置全螢幕狀態
        isFullscreen = false;
        toggleFullscreen(canvasContainer);
    };
    
    // 按鈕點擊事件
    landmarksBtn.onclick = () => {
        showLandmarks = !showLandmarks;
        landmarksBtn.style.backgroundColor = showLandmarks ? 'var(--accent-color)' : 'var(--dark-panel)';
        landmarksBtn.style.color = showLandmarks ? '#ffffff' : 'var(--dark-text)';
        if (poseResults) {
            onResults(poseResults);
        }
    };
    
    connectorsBtn.onclick = () => {
        showConnectors = !showConnectors;
        connectorsBtn.style.backgroundColor = showConnectors ? 'var(--accent-color)' : 'var(--dark-panel)';
        connectorsBtn.style.color = showConnectors ? '#ffffff' : 'var(--dark-text)';
        if (poseResults) {
            onResults(poseResults);
        }
    };
    
    // 添加懸停效果
    [landmarksBtn, connectorsBtn, fullscreenBtn].forEach(btn => {
        btn.addEventListener('mouseover', () => {
            btn.style.opacity = '0.8';
        });
        btn.addEventListener('mouseout', () => {
            btn.style.opacity = '1';
        });
    });
    
    controlsDiv.appendChild(landmarksBtn);
    controlsDiv.appendChild(connectorsBtn);
    controlsDiv.appendChild(fullscreenBtn);
    canvasContainer.appendChild(controlsDiv);
    
    // 滾輪縮放
    canvasContainer.addEventListener('wheel', (e) => {
        e.preventDefault();
        
        // 計算新的縮放比例
        const delta = e.deltaY > 0 ? 0.9 : 1.1;
        const newScale = Math.max(MIN_SCALE, Math.min(MAX_SCALE, canvasScale * delta));
        
        if (newScale !== canvasScale) {
            canvasScale = newScale;
            updateCanvasTransform();
        }
    });
    
    // 滑鼠拖曳
    canvasContainer.addEventListener('mousedown', (e) => {
        if (e.button === 0) { // 左鍵
            isDragging = true;
            lastX = e.clientX;
            lastY = e.clientY;
            canvasContainer.style.cursor = 'grabbing';
        }
    });
    
    document.addEventListener('mousemove', (e) => {
        if (isDragging) {
            const deltaX = e.clientX - lastX;
            const deltaY = e.clientY - lastY;
            
            translateX += deltaX;
            translateY += deltaY;
            
            lastX = e.clientX;
            lastY = e.clientY;
            
            updateCanvasTransform();
        }
    });
    
    document.addEventListener('mouseup', () => {
        isDragging = false;
        canvasContainer.style.cursor = 'grab';
    });
    
    // 觸控縮放
    let initialDistance = 0;
    let initialScale = 1;
    
    canvasContainer.addEventListener('touchstart', (e) => {
        if (e.touches.length === 2) {
            initialDistance = Math.hypot(
                e.touches[0].clientX - e.touches[1].clientX,
                e.touches[0].clientY - e.touches[1].clientY
            );
            initialScale = canvasScale;
        } else if (e.touches.length === 1) {
            isDragging = true;
            lastX = e.touches[0].clientX;
            lastY = e.touches[0].clientY;
        }
    });
    
    canvasContainer.addEventListener('touchmove', (e) => {
        if (e.touches.length === 2) {
            e.preventDefault();
            
            const currentDistance = Math.hypot(
                e.touches[0].clientX - e.touches[1].clientX,
                e.touches[0].clientY - e.touches[1].clientY
            );
            
            const newScale = Math.max(
                MIN_SCALE,
                Math.min(MAX_SCALE, initialScale * currentDistance / initialDistance)
            );
            
            if (newScale !== canvasScale) {
                canvasScale = newScale;
                updateCanvasTransform();
            }
        } else if (e.touches.length === 1 && isDragging) {
            e.preventDefault();
            
            const deltaX = e.touches[0].clientX - lastX;
            const deltaY = e.touches[0].clientY - lastY;
            
            translateX += deltaX;
            translateY += deltaY;
            
            lastX = e.touches[0].clientX;
            lastY = e.touches[0].clientY;
            
            updateCanvasTransform();
        }
    });
    
    canvasContainer.addEventListener('touchend', () => {
        isDragging = false;
    });
}

// 修改 updateCanvasTransform 函數
function updateCanvasTransform() {
    if (isFullscreen) {
        // 全螢幕模式下，限制平移範圍
        const maxX = (canvas.width * (canvasScale - 1)) / 2;
        const maxY = (canvas.height * (canvasScale - 1)) / 2;
        
        translateX = Math.max(-maxX, Math.min(maxX, translateX));
        translateY = Math.max(-maxY, Math.min(maxY, translateY));
    }
    
    canvas.style.transform = `translate(${translateX}px, ${translateY}px) scale(${canvasScale})`;
    canvas.style.transformOrigin = 'center center';
    
    // 更新骨架顯示
    if (poseResults) {
        onResults(poseResults);
    }
}

// 修改 toggleFullscreen 函數
function toggleFullscreen(container) {
    if (!isFullscreen) {
        // 進入全螢幕
        originalContainerStyle = {
            position: container.style.position,
            width: container.style.width,
            height: container.style.height,
            margin: container.style.margin,
            padding: container.style.padding,
            display: container.style.display,
            backgroundColor: container.style.backgroundColor,
            zIndex: container.style.zIndex
        };
        
        // 調整容器樣式
        container.style.position = 'fixed';
        container.style.top = '0';
        container.style.left = '0';
        container.style.width = '100vw';
        container.style.height = '100vh';
        container.style.zIndex = '9999';
        container.style.backgroundColor = 'var(--dark-bg)';
        container.style.margin = '0';
        container.style.padding = '0';
        container.style.display = 'flex';
        container.style.alignItems = 'center';
        container.style.justifyContent = 'center';
        
        // 調整影片元素
        video.style.position = 'absolute';
        video.style.top = '0';
        video.style.left = '0';
        video.style.width = '100%';
        video.style.height = '100%';
        video.style.objectFit = 'contain';
        
        // 調整畫布元素
        canvas.style.position = 'absolute';
        canvas.style.top = '0';
        canvas.style.left = '0';
        canvas.style.width = '100%';
        canvas.style.height = '100%';
        canvas.style.objectFit = 'contain';
        
        // 計算並設置畫布大小
        const videoAspectRatio = video.videoWidth / video.videoHeight;
        const windowAspectRatio = window.innerWidth / window.innerHeight;
        
        if (videoAspectRatio > windowAspectRatio) {
            // 以寬度為基準
            canvas.width = window.innerWidth;
            canvas.height = window.innerWidth / videoAspectRatio;
        } else {
            // 以高度為基準
            canvas.height = window.innerHeight;
            canvas.width = window.innerHeight * videoAspectRatio;
        }
        
        // 移除可能存在的舊退出按鈕
        const existingExitButton = document.querySelector('.exit-fullscreen-btn');
        if (existingExitButton) {
            document.body.removeChild(existingExitButton);
        }
        
        // 添加退出按鈕
        const exitButton = document.createElement('button');
        exitButton.className = 'tiss-btn tiss-btn-outline exit-fullscreen-btn';
        exitButton.textContent = '退出全螢幕';
        exitButton.style.position = 'fixed';
        exitButton.style.top = '20px';
        exitButton.style.right = '20px';
        exitButton.style.zIndex = '10000';
        exitButton.style.padding = '8px 16px';
        exitButton.style.fontSize = '16px';
        exitButton.style.cursor = 'pointer';
        exitButton.onclick = () => toggleFullscreen(container);
        document.body.appendChild(exitButton);
        
        // 監聽視窗大小變化
        window.addEventListener('resize', handleResize);
        
        isFullscreen = true;
        
        // 立即更新骨架顯示
        if (poseResults) {
            onResults(poseResults);
        }
    } else {
        // 退出全螢幕
        // 恢復容器樣式
        container.style.position = originalContainerStyle.position;
        container.style.width = originalContainerStyle.width;
        container.style.height = originalContainerStyle.height;
        container.style.margin = originalContainerStyle.margin;
        container.style.padding = originalContainerStyle.padding;
        container.style.display = originalContainerStyle.display;
        container.style.backgroundColor = originalContainerStyle.backgroundColor;
        container.style.zIndex = originalContainerStyle.zIndex;
        
        // 恢復影片元素樣式
        video.style.position = '';
        video.style.top = '';
        video.style.left = '';
        video.style.width = '';
        video.style.height = '';
        video.style.objectFit = '';
        
        // 恢復畫布元素樣式
        canvas.style.position = '';
        canvas.style.top = '';
        canvas.style.left = '';
        canvas.style.width = '';
        canvas.style.height = '';
        canvas.style.objectFit = '';
        
        // 恢復畫布大小
        const originalContainer = document.querySelector('.canvas-container');
        canvas.width = originalContainer.clientWidth;
        canvas.height = originalContainer.clientHeight;
        
        // 移除退出按鈕
        const exitButton = document.querySelector('.exit-fullscreen-btn');
        if (exitButton) {
            document.body.removeChild(exitButton);
        }
        
        // 移除視窗大小變化監聽器
        window.removeEventListener('resize', handleResize);
        
        isFullscreen = false;
        
        // 立即更新骨架顯示
        if (poseResults) {
            onResults(poseResults);
        }
    }
    
    // 重置縮放和平移
    resetCanvasTransform();
}

// 修改 handleResize 函數
function handleResize() {
    if (isFullscreen) {
        const videoAspectRatio = video.videoWidth / video.videoHeight;
        const windowAspectRatio = window.innerWidth / window.innerHeight;
        
        if (videoAspectRatio > windowAspectRatio) {
            // 以寬度為基準
            canvas.width = window.innerWidth;
            canvas.height = window.innerWidth / videoAspectRatio;
        } else {
            // 以高度為基準
            canvas.height = window.innerHeight;
            canvas.width = window.innerHeight * videoAspectRatio;
        }
        
        // 更新骨架顯示
        if (poseResults) {
            onResults(poseResults);
        }
    }
}

// 重置畫布位置和縮放
function resetCanvasTransform() {
    canvasScale = 1;
    translateX = 0;
    translateY = 0;
    updateCanvasTransform();
} 