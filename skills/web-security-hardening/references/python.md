# Python Security Implementation

## Rate Limiting

### Django (django-ratelimit)
```python
from django_ratelimit.decorators import ratelimit

@ratelimit(key='ip', rate='100/15m', block=True)
def api_view(request):
    return JsonResponse({'data': 'ok'})

@ratelimit(key='ip', rate='5/15m', block=True)
def login_view(request):
    # Auth logic
    pass
```

### Flask (flask-limiter)
```python
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address

limiter = Limiter(app, key_func=get_remote_address)

@app.route('/api/data')
@limiter.limit('100/15minutes')
def api_data():
    return jsonify({'data': 'ok'})

@app.route('/api/login', methods=['POST'])
@limiter.limit('5/15minutes')
def login():
    pass
```

## Security Middleware

### Django (django-secure / settings.py)
```python
# settings.py
SECURE_HSTS_SECONDS = 31536000
SECURE_HSTS_INCLUDE_SUBDOMAINS = True
SECURE_CONTENT_TYPE_NOSNIFF = True
SECURE_BROWSER_XSS_FILTER = True
X_FRAME_OPTIONS = 'DENY'
CSRF_COOKIE_SECURE = True
SESSION_COOKIE_SECURE = True

# CSP with django-csp
CSP_DEFAULT_SRC = ("'self'",)
CSP_SCRIPT_SRC = ("'self'",)
CSP_STYLE_SRC = ("'self'", "'unsafe-inline'")
```

### Flask (flask-talisman)
```python
from flask_talisman import Talisman

csp = {
    'default-src': "'self'",
    'script-src': "'self'",
    'style-src': ["'self'", "'unsafe-inline'"],
}

Talisman(app, content_security_policy=csp)
```

## CORS

### Django (django-cors-headers)
```python
# settings.py
INSTALLED_APPS = [..., 'corsheaders']
MIDDLEWARE = ['corsheaders.middleware.CorsMiddleware', ...]

CORS_ALLOWED_ORIGINS = [
    'https://yourdomain.com',
    'https://app.yourdomain.com',
]
CORS_ALLOW_CREDENTIALS = True
```

### Flask (flask-cors)
```python
from flask_cors import CORS

CORS(app, origins=['https://yourdomain.com'], supports_credentials=True)
```

## IP Block List

### Django Middleware
```python
class IPBlockMiddleware:
    BLOCKED_IPS = {'1.2.3.4', '5.6.7.8'}
    
    def __init__(self, get_response):
        self.get_response = get_response
    
    def __call__(self, request):
        ip = request.META.get('REMOTE_ADDR')
        if ip in self.BLOCKED_IPS:
            return HttpResponseForbidden('Forbidden')
        return self.get_response(request)
```

### Flask
```python
BLOCKED_IPS = {'1.2.3.4', '5.6.7.8'}

@app.before_request
def block_ips():
    if request.remote_addr in BLOCKED_IPS:
        abort(403)
```

## Input Validation (Pydantic)

```python
from pydantic import BaseModel, EmailStr, constr

class UserCreate(BaseModel):
    email: EmailStr
    password: constr(min_length=8, max_length=100)
    name: constr(min_length=1, max_length=100)

# Django view
def create_user(request):
    try:
        data = UserCreate.model_validate_json(request.body)
    except ValidationError as e:
        return JsonResponse({'errors': e.errors()}, status=400)
    # Use validated data

# Flask
@app.route('/users', methods=['POST'])
def create_user():
    try:
        data = UserCreate.model_validate(request.json)
    except ValidationError as e:
        return jsonify({'errors': e.errors()}), 400
```

## File Upload Limits

### Django
```python
# settings.py
DATA_UPLOAD_MAX_MEMORY_SIZE = 5 * 1024 * 1024  # 5MB
FILE_UPLOAD_MAX_MEMORY_SIZE = 5 * 1024 * 1024

# views.py
ALLOWED_TYPES = {'image/jpeg', 'image/png', 'application/pdf'}

def upload_file(request):
    file = request.FILES.get('file')
    if file.content_type not in ALLOWED_TYPES:
        return JsonResponse({'error': 'Invalid file type'}, status=400)
    if file.size > 5 * 1024 * 1024:
        return JsonResponse({'error': 'File too large'}, status=400)
```

### Flask
```python
app.config['MAX_CONTENT_LENGTH'] = 5 * 1024 * 1024  # 5MB

ALLOWED_EXTENSIONS = {'jpg', 'jpeg', 'png', 'pdf'}

def allowed_file(filename):
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS

@app.route('/upload', methods=['POST'])
def upload():
    file = request.files.get('file')
    if not allowed_file(file.filename):
        return jsonify({'error': 'Invalid file type'}), 400
```

## ORM Usage

### Django ORM (safe by default)
```python
# Safe - parameterized
user = User.objects.filter(email=user_input).first()

# NEVER do this
# User.objects.raw(f"SELECT * FROM users WHERE email = '{user_input}'")
```

### SQLAlchemy
```python
from sqlalchemy import select

# Safe - parameterized
stmt = select(User).where(User.email == user_input)
user = session.execute(stmt).scalar_one_or_none()

# NEVER do this
# session.execute(f"SELECT * FROM users WHERE email = '{user_input}'")
```

## Password Hashing

### Django (built-in)
```python
from django.contrib.auth.hashers import make_password, check_password

# Hash
hashed = make_password(plain_password)

# Verify
is_valid = check_password(plain_password, stored_hash)
```

### Flask / General Python (bcrypt or passlib)
```python
import bcrypt

# Hash
salt = bcrypt.gensalt(rounds=12)
hashed = bcrypt.hashpw(password.encode(), salt)

# Verify
is_valid = bcrypt.checkpw(password.encode(), stored_hash)
```

### Argon2 (recommended)
```python
from argon2 import PasswordHasher

ph = PasswordHasher()

# Hash
hashed = ph.hash(plain_password)

# Verify
try:
    ph.verify(stored_hash, plain_password)
    is_valid = True
except:
    is_valid = False
```
