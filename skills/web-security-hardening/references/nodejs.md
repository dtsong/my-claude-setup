# Node.js/Express Security Implementation

## Rate Limiting

```javascript
import rateLimit from 'express-rate-limit';

// General API limit
const apiLimiter = rateLimit({
  windowMs: 15 * 60 * 1000, // 15 minutes
  max: 100,
  standardHeaders: true,
  legacyHeaders: false,
});

// Strict limit for auth endpoints
const authLimiter = rateLimit({
  windowMs: 15 * 60 * 1000,
  max: 5,
  message: { error: 'Too many attempts, try again later' },
});

app.use('/api/', apiLimiter);
app.use('/api/auth/', authLimiter);
```

## Helmet (Security Middleware)

```javascript
import helmet from 'helmet';

app.use(helmet()); // Sets all default security headers

// Custom CSP
app.use(helmet.contentSecurityPolicy({
  directives: {
    defaultSrc: ["'self'"],
    scriptSrc: ["'self'"],
    styleSrc: ["'self'", "'unsafe-inline'"],
    imgSrc: ["'self'", "data:", "https:"],
  },
}));
```

## CORS

```javascript
import cors from 'cors';

const corsOptions = {
  origin: ['https://yourdomain.com', 'https://app.yourdomain.com'],
  methods: ['GET', 'POST', 'PUT', 'DELETE'],
  allowedHeaders: ['Content-Type', 'Authorization'],
  credentials: true,
};

app.use(cors(corsOptions));
```

## IP Block List

```javascript
const blockedIPs = new Set(['1.2.3.4', '5.6.7.8']);

const ipBlockMiddleware = (req, res, next) => {
  const clientIP = req.ip || req.connection.remoteAddress;
  if (blockedIPs.has(clientIP)) {
    console.log(`Blocked request from ${clientIP}`);
    return res.status(403).json({ error: 'Forbidden' });
  }
  next();
};

app.use(ipBlockMiddleware);
```

## Input Validation (Zod)

```javascript
import { z } from 'zod';

const userSchema = z.object({
  email: z.string().email(),
  password: z.string().min(8).max(100),
  name: z.string().min(1).max(100),
});

app.post('/api/users', (req, res) => {
  const result = userSchema.safeParse(req.body);
  if (!result.success) {
    return res.status(400).json({ errors: result.error.flatten() });
  }
  // Use result.data (validated)
});
```

## File Upload Limits (Multer)

```javascript
import multer from 'multer';

const upload = multer({
  limits: { fileSize: 5 * 1024 * 1024 }, // 5MB
  fileFilter: (req, file, cb) => {
    const allowed = ['image/jpeg', 'image/png', 'application/pdf'];
    if (allowed.includes(file.mimetype)) {
      cb(null, true);
    } else {
      cb(new Error('Invalid file type'), false);
    }
  },
  storage: multer.diskStorage({
    destination: './uploads', // Outside webroot
  }),
});

app.post('/api/upload', upload.single('file'), (req, res) => {
  res.json({ filename: req.file.filename });
});
```

## ORM (Prisma)

```javascript
import { PrismaClient } from '@prisma/client';
const prisma = new PrismaClient();

// Safe - parameterized
const user = await prisma.user.findUnique({
  where: { email: userInput },
});

// NEVER do this
// const user = await prisma.$queryRawUnsafe(`SELECT * FROM users WHERE email = '${userInput}'`);
```

## Password Hashing (bcrypt)

```javascript
import bcrypt from 'bcrypt';

const SALT_ROUNDS = 12;

// Hash password
const hash = await bcrypt.hash(plainPassword, SALT_ROUNDS);

// Verify password
const isValid = await bcrypt.compare(plainPassword, storedHash);
```

## Auth Middleware

```javascript
import jwt from 'jsonwebtoken';

const authMiddleware = (req, res, next) => {
  const authHeader = req.headers.authorization;
  if (!authHeader?.startsWith('Bearer ')) {
    return res.status(401).json({ error: 'Missing token' });
  }
  
  try {
    const token = authHeader.split(' ')[1];
    const decoded = jwt.verify(token, process.env.JWT_SECRET);
    req.user = decoded;
    next();
  } catch {
    return res.status(401).json({ error: 'Invalid token' });
  }
};

app.use('/api/protected', authMiddleware);
```
